const WIDTH: usize = 3;
#[allow(non_upper_case_globals)]
const R_f: usize = 3;
const R_P: usize = 2;
const R: usize = 2 * R_f + R_P;

use halo2::{
    arithmetic::{Field, FieldExt},
    circuit::{layouter::SingleChipLayouter, Cell, Chip, Layouter},
    dev::{MockProver, VerifyFailure},
    pasta::Fp,
    plonk::{
        Advice, Assignment, Circuit, Column, ConstraintSystem, Error, Fixed, Instance, Permutation,
        Selector,
    },
    poly::Rotation,
};
use lazy_static::lazy_static;
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;

lazy_static! {
    static ref PRE_KEYS: Vec<Fp> = rand_pre_keys([1; 32]);
    static ref POST_KEYS: Vec<Vec<Fp>> = rand_post_keys([2; 32]);
    static ref MDS: Vec<Vec<Fp>> = rand_matrix([3; 32]);
    static ref PRE_SPARSE: Vec<Vec<Fp>> = rand_matrix([4; 32]);
    static ref SPARSE: Vec<Vec<Vec<Fp>>> = (0..R_P)
        .map(|i| rand_matrix([5 + i as u8; 32]))
        .collect();

    /*
    static ref PRE_KEYS: Vec<Fp> = vec![Fp::from(1), Fp::from(2), Fp::from(3)];
    static ref POST_KEYS: Vec<Vec<Fp>> = vec![
        vec![Fp::from(1), Fp::from(2), Fp::from(3)],
        vec![Fp::from(4), Fp::from(5), Fp::from(6)],
        vec![Fp::from(7), Fp::from(8), Fp::from(9)],
        vec![Fp::from(1)],
        vec![Fp::from(2)],
        vec![Fp::from(3), Fp::from(4), Fp::from(5)],
        vec![Fp::from(6), Fp::from(7), Fp::from(8)],
        vec![],
    ];
    static ref MDS: Vec<Vec<Fp>> = vec![
        vec![Fp::from(1), Fp::from(2), Fp::from(3)],
        vec![Fp::from(4), Fp::from(5), Fp::from(6)],
        vec![Fp::from(7), Fp::from(8), Fp::from(9)],
    ];
    static ref PRE_SPARSE: Vec<Vec<Fp>> = vec![
        vec![Fp::from(3), Fp::from(4), Fp::from(5)],
        vec![Fp::from(6), Fp::from(7), Fp::from(8)],
        vec![Fp::from(9), Fp::from(1), Fp::from(2)],
    ];
    static ref SPARSE: Vec<Vec<Vec<Fp>>> = vec![
        vec![
            vec![Fp::from(5), Fp::from(6), Fp::from(7)],
            vec![Fp::from(8), Fp::from(9), Fp::from(1)],
            vec![Fp::from(2), Fp::from(3), Fp::from(4)],
        ],
        vec![
            vec![Fp::from(7), Fp::from(8), Fp::from(9)],
            vec![Fp::from(1), Fp::from(2), Fp::from(3)],
            vec![Fp::from(4), Fp::from(5), Fp::from(6)],
        ],
    ];
    */
}

fn rand_pre_keys(seed: [u8; 32]) -> Vec<Fp> {
    let mut rng = ChaCha8Rng::from_seed(seed);
    (0..WIDTH)
        .map(|_| Fp::from(rng.gen::<u64>()))
        .collect()
}

fn rand_post_keys(seed: [u8; 32]) -> Vec<Vec<Fp>> {
    let mut rng = ChaCha8Rng::from_seed(seed);
    (0..R)
        .map(|round| {
            if is_full_round(round) && round != R - 1 {
                (0..WIDTH).map(|_| Fp::random(&mut rng)).collect()
            } else if is_partial_round(round) {
                vec![Fp::random(&mut rng)]
            } else {
                vec![]
            }
        })
        .collect()
}

fn rand_matrix(seed: [u8; 32]) -> Vec<Vec<Fp>> {
    let mut rng = ChaCha8Rng::from_seed(seed);
    (0..WIDTH)
        // .map(|_| (0..WIDTH).map(|_| Fp::random(&mut rng)).collect())
        .map(|_| (0..WIDTH).map(|_| Fp::from(rng.gen::<u64>())).collect())
        .collect()
}

fn is_full_round(round: usize) -> bool {
    round < R_f || round >= R_f + R_P
}

fn is_partial_round(round: usize) -> bool {
    round >= R_f && round < R_f + R_P
}

fn pow5(x: Fp) -> Fp {
    x.square().square() * x
}

fn sbox_pre_post(state: &[Fp]) -> Vec<Fp> {
    (0..WIDTH)
        .map(|i| pow5(state[i] + PRE_KEYS[i]) + POST_KEYS[0][i])
        .collect()
}

fn sbox_post(state: &[Fp], post_keys: &[Fp]) -> Vec<Fp> {
    (0..WIDTH)
        .map(|i| pow5(state[i]) + post_keys[i])
        .collect()
}

fn sbox_no_add(state: &[Fp]) -> Vec<Fp> {
    (0..WIDTH)
        .map(|i| pow5(state[i]))
        .collect()
}

fn vec_matrix_mul(v: &[Fp], m: &[Vec<Fp>]) -> Vec<Fp> {
    let n = v.len();
    assert_eq!(m.len(), n);
    (0..n)
        .map(|col| {
            let mut lc = Fp::zero();
            for i in 0..n {
                lc += v[i] * m[i][col];
            }
            lc
        })
        .collect()
}

fn poseidon(preimg: &[Fp]) -> Fp {
    let mut state = sbox_pre_post(&preimg);
    state = vec_matrix_mul(&state, &*MDS);

    for round in 1..R_f {
        state = sbox_post(&state, &*POST_KEYS[round]);
        let m = if round == R_f - 1 { &*PRE_SPARSE } else { &*MDS };
        state = vec_matrix_mul(&state, m);
    }

    for round in R_f..R_f + R_P {
        state[0] = pow5(state[0].clone()) + POST_KEYS[round][0];
        let sparse_index = round - R_f;
        state = vec_matrix_mul(&state, &*SPARSE[sparse_index]);
    }

    for round in R_f + R_P..R - 1 {
        state = sbox_post(&state, &*POST_KEYS[round]);
        state = vec_matrix_mul(&state, &*MDS);
    }

    state = sbox_no_add(&state);
    state = vec_matrix_mul(&state, &*MDS);
    state[1]
}

#[derive(Clone, Debug)]
struct Alloc {
    cell: Cell,
    value: Fp,
}

struct PoseidonChip {
    config: PoseidonChipConfig,
}

#[derive(Clone, Debug)]
struct PoseidonChipConfig {
    a_col: Column<Advice>,
    sbox_out_col: Column<Advice>,
    mds_out_col: Column<Advice>,
    pre_key_col: Column<Fixed>,
    post_key_col: Column<Fixed>,
    mds_cols: Vec<Column<Fixed>>,
    s_sbox_pre_post: Selector,
    s_sbox_post: Selector,
    s_sbox_no_add: Selector,
    s_mds: Vec<Selector>,
    perm_output_to_input: Permutation,
    perm_output_to_sbox_output: Permutation,
    perm_preimg: Vec<Permutation>,
}


impl Chip<Fp> for PoseidonChip {
    type Config = PoseidonChipConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl PoseidonChip {
    fn new(config: PoseidonChipConfig) -> Self {
        PoseidonChip { config }
    }

    fn configure(cs: &mut ConstraintSystem<Fp>) ->
        (PoseidonChipConfig, Vec<Column<Advice>>, Column<Advice>)
    {
        let a_col = cs.advice_column();
        let sbox_out_col = cs.advice_column();
        let mds_out_col = cs.advice_column();
        let pre_key_col = cs.fixed_column();
        let post_key_col = cs.fixed_column();
        let mds_cols = vec![cs.fixed_column(), cs.fixed_column(), cs.fixed_column()];

        let s_sbox_pre_post = cs.selector();
        let s_sbox_post = cs.selector();
        let s_sbox_no_add = cs.selector();
        let s_mds = vec![cs.selector(), cs.selector(), cs.selector()];

        cs.create_gate("s_sbox_pre_post", |cs| {
            let a = cs.query_advice(a_col, Rotation::cur());
            let pre_key = cs.query_fixed(pre_key_col, Rotation::cur());
            let post_key = cs.query_fixed(post_key_col, Rotation::cur());
            let sbox_out = cs.query_advice(sbox_out_col, Rotation::cur());
            let s_sbox_pre_post = cs.query_selector(s_sbox_pre_post, Rotation::cur());
            // (a + pre_key)^5 + post_key = out
            let a_plus_pre = a + pre_key;
            s_sbox_pre_post * (
                a_plus_pre.clone() * a_plus_pre.clone() * a_plus_pre.clone() * a_plus_pre.clone() *
                a_plus_pre + post_key - sbox_out
            )
        });

        cs.create_gate("s_sbox_post", |cs| {
            let a = cs.query_advice(a_col, Rotation::cur());
            let post_key = cs.query_fixed(post_key_col, Rotation::cur());
            let sbox_out = cs.query_advice(sbox_out_col, Rotation::cur());
            let s_sbox_post = cs.query_selector(s_sbox_post, Rotation::cur());
            // a^5 + post_key = b
            s_sbox_post * (a.clone() * a.clone() * a.clone() * a.clone() * a + post_key - sbox_out)
        });

        cs.create_gate("s_sbox_no_add", |cs| {
            let a = cs.query_advice(a_col, Rotation::cur());
            let sbox_out = cs.query_advice(sbox_out_col, Rotation::cur());
            let s_sbox_no_add = cs.query_selector(s_sbox_no_add, Rotation::cur());
            // a^5 = b
            s_sbox_no_add * (a.clone() * a.clone() * a.clone() * a.clone() * a - sbox_out)
        });

        // Calculates the dot product of the sbox outputs with column `0` of the MDS matrix. Note
        // that `s_mds_0` is enabled in the first MDS row.
        cs.create_gate("s_mds_0", |cs| {
            let sbox_out_0 = cs.query_advice(sbox_out_col, Rotation::cur());
            let sbox_out_1 = cs.query_advice(sbox_out_col, Rotation::next());
            let sbox_out_2 = cs.query_advice(sbox_out_col, Rotation(2));
            let mds_out_0 = cs.query_advice(mds_out_col, Rotation::cur());
            let s_mds_0 = cs.query_selector(s_mds[0], Rotation::cur());

            // The first MDS column.
            let m_0 = cs.query_fixed(mds_cols[0], Rotation::cur());
            let m_1 = cs.query_fixed(mds_cols[0], Rotation::next());
            let m_2 = cs.query_fixed(mds_cols[0], Rotation(2));

            // Dot product of sbox outputs with the first MDS column.
            s_mds_0 * (sbox_out_0 * m_0 + sbox_out_1 * m_1 + sbox_out_2 * m_2 - mds_out_0)
        });

        // Calculates the dot product of the sbox outputs with column `1` of the MDS matrix. Note
        // that `s_mds_1` is enabled in the second MDS row.
        cs.create_gate("s_mds_1", |cs| {
            let sbox_out_0 = cs.query_advice(sbox_out_col, Rotation::prev());
            let sbox_out_1 = cs.query_advice(sbox_out_col, Rotation::cur());
            let sbox_out_2 = cs.query_advice(sbox_out_col, Rotation::next());
            let mds_out_1 = cs.query_advice(mds_out_col, Rotation::cur());
            let s_mds_1 = cs.query_selector(s_mds[1], Rotation::cur());

            // The second MDS column.
            let m_0 = cs.query_fixed(mds_cols[1], Rotation::prev());
            let m_1 = cs.query_fixed(mds_cols[1], Rotation::cur());
            let m_2 = cs.query_fixed(mds_cols[1], Rotation::next());

            // Dot product of the sbox outputs with the second MDS column.
            s_mds_1 * (sbox_out_0 * m_0 + sbox_out_1 * m_1 + sbox_out_2 * m_2 - mds_out_1)
        });

        // Calculates the dot product of the sbox outputs with column `2` of the MDS matrix. Note
        // that `s_mds_2` is enabled in the third MDS row.
        cs.create_gate("s_mds_2", |cs| {
            let sbox_out_0 = cs.query_advice(sbox_out_col, Rotation(-2));
            let sbox_out_1 = cs.query_advice(sbox_out_col, Rotation::prev());
            let sbox_out_2 = cs.query_advice(sbox_out_col, Rotation::cur());
            let mds_out_2 = cs.query_advice(mds_out_col, Rotation::cur());
            let s_mds_2 = cs.query_selector(s_mds[2], Rotation::cur());

            // The third MDS column.
            let m_0 = cs.query_fixed(mds_cols[2], Rotation(-2));
            let m_1 = cs.query_fixed(mds_cols[2], Rotation::prev());
            let m_2 = cs.query_fixed(mds_cols[2], Rotation::cur());

            // Dot product of the sbox outputs with the third MDS column.
            s_mds_2 * (sbox_out_0 * m_0 + sbox_out_1 * m_1 + sbox_out_2 * m_2 - mds_out_2)
        });

        // Copies a round's MDS output into the next round's state.
        let perm_output_to_input =
            Permutation::new(cs, &[mds_out_col.into(), a_col.into()]);

        // Copies a round's MDS output into the next round's sbox output.
        let perm_output_to_sbox_output =
            Permutation::new(cs, &[mds_out_col.into(), sbox_out_col.into()]);

        // Copy the first, second, and third preimage elements into the first column.
        let perm_preimg = {
            let perm_a_to_a = Permutation::new(cs, &[a_col.into()]);
            let perm_sbox_out_to_a = Permutation::new(cs, &[sbox_out_col.into(), a_col.into()]);
            let perm_mds_out_to_a = perm_output_to_input.clone();
            vec![perm_a_to_a, perm_sbox_out_to_a, perm_mds_out_to_a]
        };

        let poseidon_config = PoseidonChipConfig {
            a_col,
            sbox_out_col,
            mds_out_col,
            pre_key_col,
            post_key_col,
            mds_cols,
            s_sbox_pre_post,
            s_sbox_post,
            s_sbox_no_add,
            s_mds,
            perm_output_to_input,
            perm_output_to_sbox_output,
            perm_preimg,
        };
        let preimg_cols = vec![a_col, sbox_out_col, mds_out_col];
        let digest_col = mds_out_col;
        (poseidon_config, preimg_cols, digest_col)
    }

    fn hash(
        &self,
        layouter: &mut impl Layouter<Fp>,
        preimg_alloc: Vec<Alloc>,
    ) -> Result<Alloc, Error> {
        let mut state_alloc = preimg_alloc;

        for round in 0..R_f {
            state_alloc = self.alloc_full_round(layouter, &state_alloc, round)?;
        }

        for round in R_f..R_f + R_P {
            state_alloc = self.alloc_partial_round(layouter, &state_alloc, round)?;
        }

        for round in R_f + R_P..R {
            state_alloc = self.alloc_full_round(layouter, &state_alloc, round)?;
        }

        Ok(state_alloc.remove(1))
    }

    fn alloc_full_round(
        &self,
        layouter: &mut impl Layouter<Fp>,
        state_alloc: &[Alloc],
        round: usize,
    ) -> Result<Vec<Alloc>, Error> {
        assert!(is_full_round(round));
        assert_eq!(state_alloc.len(), WIDTH);

        let is_first_round = round == 0;
        let is_last_round = round == R - 1;
        let is_pre_sparse_round = round == R_f - 1;

        let post_keys = &*POST_KEYS[round];
        assert_eq!(post_keys.len(), if is_last_round { 0 } else { WIDTH });

        // Copy field elements out of the `Alloc`'s for easier arithmetic.
        let state_values: Vec<Fp> = state_alloc
            .iter()
            .map(|alloc| alloc.value)
            .collect();

        // Calculate the S-box output for each state element.
        let sbox_outputs = if is_first_round {
            sbox_pre_post(&state_values)
        } else if is_last_round {
            sbox_no_add(&state_values)
        } else {
            sbox_post(&state_values, &post_keys)
        };

        // Calculate the MDS mixing output for each state element.
        let m = if is_pre_sparse_round { &*PRE_SPARSE } else { &*MDS };
        let mds_outputs = vec_matrix_mul(&sbox_outputs, m);

        // Store the allocated outputs of MDS mixing.
        let mut mds_outputs_alloc: Vec<Option<Alloc>> = vec![None; WIDTH];

        layouter.assign_region(
            || format!("alloc (full) round {}", round),
            |mut region| {
                for row_offset in 0..WIDTH {
                    let a_cell = region.assign_advice(
                        || format!("a_{} (round {})", row_offset, round),
                        self.config.a_col,
                        row_offset,
                        || Ok(state_values[row_offset]),
                    )?;

                    // If this is the first round, we reallocate values from the preimage row.
                    // Otherwise, we reallocate values output by the previous round.
                    let perm = if is_first_round {
                        &self.config.perm_preimg[row_offset]
                    } else {
                        &self.config.perm_output_to_input
                    };
                    region.constrain_equal(perm, state_alloc[row_offset].cell, a_cell)?;

                    // If this is the first round allocate a pre-S-box key.
                    if is_first_round {
                        region.assign_fixed(
                            || format!("pre_key_{} (round {})", row_offset, round),
                            self.config.pre_key_col,
                            row_offset,
                            || Ok(PRE_KEYS[row_offset]),
                        )?;
                    }

                    // If this is not the last round allocate a post-S-box key.
                    if !is_last_round {
                        region.assign_fixed(
                            || format!("post_key_{} (round {})", row_offset, round),
                            self.config.post_key_col,
                            row_offset,
                            || Ok(post_keys[row_offset]),
                        )?;
                    }

                    // Allocate the S-box output.
                    region.assign_advice(
                        || format!("sbox_out_{} (round {})", row_offset, round),
                        self.config.sbox_out_col,
                        row_offset,
                        || Ok(sbox_outputs[row_offset]),
                    )?;

                    // Allocate the MDS mixing output.
                    let mds_output_cell = region.assign_advice(
                        || format!("mds_out_{} (round {})", row_offset, round),
                        self.config.mds_out_col,
                        row_offset,
                        || Ok(mds_outputs[row_offset]),
                    )?;

                    // Keep a reference to the allocated MDS output.
                    mds_outputs_alloc[row_offset] = Some(Alloc {
                        cell: mds_output_cell,
                        value: mds_outputs[row_offset],
                    });

                    // Enable the S-box and MDS mixing selectors.
                    if is_first_round {
                        self.config.s_sbox_pre_post.enable(&mut region, row_offset)?;
                    } else if is_last_round {
                        self.config.s_sbox_no_add.enable(&mut region, row_offset)?;
                    } else {
                        self.config.s_sbox_post.enable(&mut region, row_offset)?;
                    };
                    self.config.s_mds[row_offset].enable(&mut region, row_offset)?;

                    // Allocate this MDS matrix row.
                    for col in 0..WIDTH {
                        region.assign_fixed(
                            || format!(
                                "{} row={}, col={} (round {})",
                                if is_pre_sparse_round { "P" } else { "MDS" },
                                row_offset,
                                col,
                                round,
                            ),
                            self.config.mds_cols[col],
                            row_offset,
                            || Ok(m[row_offset][col]),
                        )?;
                    }
                }
                Ok(())
            },
        )?;

        let mds_outputs_alloc: Vec<Alloc> = mds_outputs_alloc
            .into_iter()
            .map(|opt| opt.unwrap())
            .collect();

        Ok(mds_outputs_alloc)
    }

    fn alloc_partial_round(
        &self,
        layouter: &mut impl Layouter<Fp>,
        state_alloc: &[Alloc],
        round: usize,
    ) -> Result<Vec<Alloc>, Error> {
        assert!(is_partial_round(round));
        assert_eq!(state_alloc.len(), WIDTH);

        assert_eq!(POST_KEYS[round].len(), 1);
        let post_key = POST_KEYS[round][0];

        // Copy field elements out of `Alloc`'s for easier arithmetic.
        let state_values: Vec<Fp> = state_alloc
            .iter()
            .map(|alloc| alloc.value)
            .collect();

        // Calculate the S-box output for the first state element.
        let mut sbox_outputs: Vec<Fp> = vec![pow5(state_values[0]) + post_key];
        sbox_outputs.extend_from_slice(&state_values[1..]);

        // Calculate the MDS mixing output for each state element.
        let sparse_index = round - R_f;
        let m = &*SPARSE[sparse_index];
        let mds_outputs = vec_matrix_mul(&sbox_outputs, m);

        // Store the allocated outputs of MDS mixing.
        let mut mds_outputs_alloc: Vec<Option<Alloc>> = vec![None; WIDTH];

        layouter.assign_region(
            || format!("alloc (partial) round {}", round),
            |mut region| {
                // Allocate values that are exclusive to the first row.
                let row_offset = 0;

                // Reallocate the first state element which was output by the previous round.
                let a_cell = region.assign_advice(
                    || format!("a_0 (round {})", round),
                    self.config.a_col,
                    row_offset,
                    || Ok(state_values[0]),
                )?;

                region.constrain_equal(
                    &self.config.perm_output_to_input,
                    state_alloc[0].cell,
                    a_cell,
                )?;

                // Allocate the first state element's post-S-box key.
                region.assign_fixed(
                    || format!("post_key_0 (round {})", round),
                    self.config.post_key_col,
                    row_offset,
                    || Ok(post_key),
                )?;

                // Enable the first state element's S-box selector.
                self.config.s_sbox_post.enable(&mut region, row_offset)?;

                // Allocate the remaining round values.
                for row_offset in 0..WIDTH {
                    // If this is the first row (`row_offset = 0`), allocate the first state
                    // element's S-box output. If this is not the first row, reallocate the state
                    // element output by the previous round.
                    let sbox_out_cell = region.assign_advice(
                        || format!("sbox_out_{} (round {})", row_offset, round),
                        self.config.sbox_out_col,
                        row_offset,
                        || Ok(sbox_outputs[row_offset]),
                    )?;

                    if row_offset > 0 {
                        region.constrain_equal(
                            &self.config.perm_output_to_sbox_output,
                            state_alloc[row_offset].cell,
                            sbox_out_cell,
                        )?;
                    }

                    // Allocate the state element's MDS mixing output.
                    let mds_out_cell = region.assign_advice(
                        || format!("mds_out_{} (round {})", row_offset, round),
                        self.config.mds_out_col,
                        row_offset,
                        || Ok(mds_outputs[row_offset]),
                    )?;

                    // Keep a reference to the allocated MDS output.
                    mds_outputs_alloc[row_offset] = Some(Alloc {
                        cell: mds_out_cell,
                        value: mds_outputs[row_offset],
                    });

                    // Enable the MDS mixing selector for this state element.
                    self.config.s_mds[row_offset].enable(&mut region, row_offset)?;

                    // Allocate this MDS matrix row.
                    for col in 0..WIDTH {
                        region.assign_fixed(
                            || format!(
                                "S{} row={}, col={} (round {})",
                                sparse_index,
                                row_offset,
                                col,
                                round,
                            ),
                            self.config.mds_cols[col],
                            row_offset,
                            || Ok(m[row_offset][col]),
                        )?;
                    }
                }
                Ok(())
            },
        )?;

        let mds_outputs_alloc: Vec<Alloc> = mds_outputs_alloc
            .into_iter()
            .map(|opt| opt.unwrap())
            .collect();

        Ok(mds_outputs_alloc)
    }
}

struct HasherCircuit {
    // Private inputs.
    preimg: Vec<Fp>,
}

#[derive(Clone)]
struct HasherCircuitConfig {
    preimg_cols: Vec<Column<Advice>>,
    digest_col: Column<Advice>,
    pub_col: Column<Instance>,
    s_pub: Selector,
    perm_digest: Permutation,
    poseidon_config: PoseidonChipConfig,
}

impl Circuit<Fp> for HasherCircuit {
    type Config = HasherCircuitConfig;

    fn configure(cs: &mut ConstraintSystem<Fp>) -> Self::Config {
        let (poseidon_config, preimg_cols, digest_col) = PoseidonChip::configure(cs);
        let perm_digest = Permutation::new(cs, &[digest_col.into()]);
        let pub_col = cs.instance_column();
        let s_pub = cs.selector();

        cs.create_gate("public input", |cs| {
            let digest = cs.query_advice(digest_col, Rotation::cur());
            let pi = cs.query_instance(pub_col, Rotation::cur());
            let s_pub = cs.query_selector(s_pub, Rotation::cur());
            s_pub * (digest - pi)
        });

        HasherCircuitConfig {
            preimg_cols,
            digest_col,
            pub_col,
            s_pub,
            perm_digest,
            poseidon_config,
        }
    }

    fn synthesize(&self, cs: &mut impl Assignment<Fp>, config: Self::Config) -> Result<(), Error> {
        assert_eq!(self.preimg.len(), WIDTH);
        let mut layouter = SingleChipLayouter::new(cs)?;
        let poseidon_chip = PoseidonChip::new(config.poseidon_config.clone());

        // Allocate the preimage in the first row of the constraint system.
        let mut preimg_alloc: Vec<Option<Alloc>> = vec![None; WIDTH];

        layouter.assign_region(
            || "alloc preimage",
            |mut region| {
                let row_offset = 0;
                for i in 0..WIDTH {
                    let preimg_cell = region.assign_advice(
                        || format!("preimg_{}", i),
                        config.preimg_cols[i],
                        row_offset,
                        || Ok(self.preimg[i]),
                    )?;
                    preimg_alloc[i] = Some(Alloc {
                        cell: preimg_cell,
                        value: self.preimg[i].clone(),
                    });
                }
                Ok(())
            },
        )?;

        let preimg_alloc: Vec<Alloc> = preimg_alloc.into_iter().map(|opt| opt.unwrap()).collect();
        let digest_alloc = poseidon_chip.hash(&mut layouter, preimg_alloc)?;
        dbg!(digest_alloc.value);

        // Copy the digest out of the chip and check that agrees with the public input.
        layouter.assign_region(
            || "digest equality",
            |mut region| {
                let row_offset = 0;
                let copied_digest_cell = region.assign_advice(
                    || "copied digest",
                    config.digest_col,
                    row_offset,
                    || Ok(digest_alloc.value),
                )?;
                region.constrain_equal(&config.perm_digest, digest_alloc.cell, copied_digest_cell)?;
                config.s_pub.enable(&mut region, row_offset)?;
                Ok(())
            },
        )?;

        Ok(())
    }
}

fn main() {
    // There are `WIDTH` number of rows per round; add one row for allocating the preimage and one
    // row for checking that the calculated digest agrees with the public input digest.
    const N_ROWS_USED: u32 = (R * WIDTH + 2) as u32;
    const PUB_INPUT_ROW_INDEX: usize = N_ROWS_USED as usize - 1;

    // The public digest.
    let pub_input = Fp::from_bytes(&[
        92, 156, 142, 19, 149, 223, 255, 67, 5, 168,
        243, 206, 123, 14, 94, 31, 226, 187, 207, 47,
        97, 158, 70, 2, 132, 63, 106, 142, 219, 243,
        144, 17,
    ]).unwrap();

    // Verifier's public inputs.
    let k = (N_ROWS_USED as f32).log2().ceil() as u32;
    let n_rows = 1 << k;
    let mut pub_inputs = vec![Fp::zero(); n_rows];
    pub_inputs[PUB_INPUT_ROW_INDEX] = Fp::from(pub_input);

    // Prover's private inputs.
    let preimg = vec![Fp::from(55), Fp::from(101), Fp::from(237)];
    dbg!(poseidon(&preimg));
    // println!("{:?}", poseidon(&preimg).to_bytes());
    let circuit = HasherCircuit { preimg };

    let prover = MockProver::run(k, &circuit, vec![pub_inputs.clone()]).unwrap();
    // dbg!(prover.verify());
    assert!(prover.verify().is_ok());
}
