// The constraint system matrix for an arity-2 Merkle tree of 8 leaves using a mocked hasher (one
// selector/gate `s_hash` and one allocation `digest = (l + GAMMA) * (r + GAMMA)` for a random
// gamma and Merkle left/right inputs `l` and `r`).

// |-----||------------------|------------------|----------|---------|-------|---------|--------|--------|
// | row ||       a_col      |       b_col      |  c_col   | pub_col | s_pub | s_bool  | s_swap | s_hash |
// |-----||------------------|------------------|----------|---------|-------|---------|--------|--------|
// |  0  ||       leaf       |      elem_1      |  cbit_1  | cbit_1  |   1   |    1    |    1   |    0   |
// |  1  ||    leaf/elem_1   |   leaf/elem_1    | digest_1 |         |   0   |    0    |    0   |    1   |
// |  2  ||     digest_1*    |      elem_2      |  cbit_2  | cbit_2  |   1   |    1    |    1   |    0   |
// |  3  || digest_1/elem_2  | digest_1/elem_2  | digest_2 |         |   0   |    0    |    0   |    1   |
// |  4  ||     digest_2*    |       elem_3     |  cbit_3  | cbit_3  |   1   |    1    |    1   |    0   |
// |  5  || digest_2/elem_3  | digest_2/elem_3  | digest_3 |  root   |   1   |    0    |    0   |    1   |
// |-----||------------------|------------------|----------|---------|-------|---------|--------|--------|
//   "*" = copy

use ff::Field;
use halo2::{
    circuit::{layouter::SingleChipLayouter, Cell, Chip, Layouter},
    dev::{MockProver, VerifyFailure},
    pasta::Fp,
    plonk::{
        Advice, Assignment, Circuit, Column, ConstraintSystem, Error, Expression, Instance,
        Permutation, Selector,
    },
    poly::Rotation,
};
use lazy_static::lazy_static;
use rand::{thread_rng, Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;

// The number of leafs in the Merkle tree. This value can be changed to any power of two.
const N_LEAFS: usize = 8;
const PATH_LEN: usize = N_LEAFS.trailing_zeros() as usize;
const TREE_LAYERS: usize = PATH_LEN + 1;

// The number of rows used in the constraint system matrix (two rows per path element).
const N_ROWS_USED: usize = 2 * PATH_LEN;
const LAST_ROW: usize = N_ROWS_USED - 1;

lazy_static! {
    static ref GAMMA: Fp = Fp::random(ChaCha8Rng::from_seed([101u8; 32]));
}

// This serves as a mock hash function because the Poseidon chip has not yet been implemented.
fn mock_hash(a: Fp, b: Fp) -> Fp {
    (a + *GAMMA) * (b + *GAMMA)
}

struct Alloc {
    cell: Cell,
    value: Fp,
}

enum MaybeAlloc {
    Alloc(Alloc),
    Unalloc(Fp),
}

impl MaybeAlloc {
    fn value(&self) -> Fp {
        match self {
            MaybeAlloc::Alloc(alloc) => alloc.value.clone(),
            MaybeAlloc::Unalloc(value) => value.clone(),
        }
    }

    fn cell(&self) -> Cell {
        match self {
            MaybeAlloc::Alloc(alloc) => alloc.cell.clone(),
            MaybeAlloc::Unalloc(_) => unreachable!(),
        }
    }
}

struct MerkleChip {
    config: MerkleChipConfig,
}

#[derive(Clone, Debug)]
struct MerkleChipConfig {
    a_col: Column<Advice>,
    b_col: Column<Advice>,
    c_col: Column<Advice>,
    pub_col: Column<Instance>,
    s_pub: Selector,
    s_bool: Selector,
    s_swap: Selector,
    s_hash: Selector,
    perm_digest: Permutation,
}

impl Chip<Fp> for MerkleChip {
    type Config = MerkleChipConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl MerkleChip {
    fn new(config: MerkleChipConfig) -> Self {
        MerkleChip { config }
    }

    fn configure(cs: &mut ConstraintSystem<Fp>) -> MerkleChipConfig {
        let a_col = cs.advice_column();
        let b_col = cs.advice_column();
        let c_col = cs.advice_column();
        let pub_col = cs.instance_column();

        let s_pub = cs.selector();
        let s_bool = cs.selector();
        let s_swap = cs.selector();
        let s_hash = cs.selector();

        cs.create_gate("public input", |cs| {
            let c = cs.query_advice(c_col, Rotation::cur());
            let pi = cs.query_instance(pub_col, Rotation::cur());
            let s_pub = cs.query_selector(s_pub, Rotation::cur());
            s_pub * (c - pi)
        });

        cs.create_gate("boolean constrain", |cs| {
            let c = cs.query_advice(c_col, Rotation::cur());
            let s_bool = cs.query_selector(s_bool, Rotation::cur());
            s_bool * c.clone() * (Expression::Constant(Fp::one()) - c)
        });

        // |-------|-------|-------|--------|
        // | a_col | b_col | c_col | s_swap |
        // |-------|-------|-------|--------|
        // |   a   |   b   |  bit  |    1   |
        // |   l   |   r   |       |        |
        // |-------|-------|-------|--------|
        // where:
        //     bit = 0  ==>  l = a, r = b
        //     bit = 1  ==>  l = b, r = a
        //
        // Choose left gate:
        //     logic: let l = if bit == 0 { a } else { b }
        //     poly:  bit * (b - a) - (l - a) = 0
        //
        // Choose right gate:
        //     logic: let r = if bit == 0 { b } else { a }
        //     poly:  bit * (b - a) - (b - r) = 0
        //
        // Swap gate = choose left + choose right:
        //     logic: let (l, r) = if bit == 0 { (a, b) } else { (b, a) }
        //     poly: bit * (b - a) - (l - a) + bit * (b - a) - (b - r) = 0
        //           bit * 2 * (b - a)  - (l - a) - (b - r) = 0
        cs.create_gate("swap", |cs| {
            let a = cs.query_advice(a_col, Rotation::cur());
            let b = cs.query_advice(b_col, Rotation::cur());
            let bit = cs.query_advice(c_col, Rotation::cur());
            let s_swap = cs.query_selector(s_swap, Rotation::cur());
            let l = cs.query_advice(a_col, Rotation::next());
            let r = cs.query_advice(b_col, Rotation::next());
            s_swap * ((bit * Fp::from(2) * (b.clone() - a.clone()) - (l - a)) - (b - r))
        });

        // (l + gamma) * (r + gamma) = digest
        cs.create_gate("hash", |cs| {
            let l = cs.query_advice(a_col, Rotation::cur());
            let r = cs.query_advice(b_col, Rotation::cur());
            let digest = cs.query_advice(c_col, Rotation::cur());
            let s_hash = cs.query_selector(s_hash, Rotation::cur());
            s_hash * ((l + Expression::Constant(*GAMMA)) * (r + Expression::Constant(*GAMMA)) - digest)
        });

        let perm_digest = Permutation::new(cs, &[c_col.into(), a_col.into()]);

        MerkleChipConfig {
            a_col,
            b_col,
            c_col,
            pub_col,
            s_pub,
            s_bool,
            s_swap,
            s_hash,
            perm_digest,
        }
    }

    fn hash_leaf_layer(
        &self,
        layouter: &mut impl Layouter<Fp>,
        leaf: Fp,
        path_elem: Fp,
        c_bit: Fp,
    ) -> Result<Alloc, Error> {
        self.hash_layer_inner(layouter, MaybeAlloc::Unalloc(leaf), path_elem, c_bit, 0)
    }

    fn hash_non_leaf_layer(
        &self,
        layouter: &mut impl Layouter<Fp>,
        prev_digest: Alloc,
        path_elem: Fp,
        c_bit: Fp,
        layer: usize,
    ) -> Result<Alloc, Error> {
        self.hash_layer_inner(layouter, MaybeAlloc::Alloc(prev_digest), path_elem, c_bit, layer)
    }

    fn hash_layer_inner(
        &self,
        layouter: &mut impl Layouter<Fp>,
        leaf_or_digest: MaybeAlloc,
        path_elem: Fp,
        c_bit: Fp,
        layer: usize,
    ) -> Result<Alloc, Error> {
        let mut digest_alloc: Option<Alloc> = None;

        layouter.assign_region(
            || "leaf layer",
            |mut region| {
                let mut row_offset = 0;

                // Allocate in `a_col` either the leaf or reallocate the previous tree layer's
                // calculated digest (stored in the previous row's `c_col`).
                let a_value = leaf_or_digest.value();

                let a_cell = region.assign_advice(
                    || format!("{} (layer {})", if layer == 0 { "leaf" } else { "a" }, layer),
                    self.config.a_col,
                    row_offset,
                    || Ok(a_value),
                )?;

                if layer > 0 {
                    let prev_digest_cell = leaf_or_digest.cell();
                    region.constrain_equal(&self.config.perm_digest, prev_digest_cell, a_cell)?;
                }

                // Allocate private inputs for this tree layer's path element and challenge bit (in
                // columns `b_col` and `c_col` respectively). Expose the challenge bit as a public
                // input.
                let _elem_cell = region.assign_advice(
                    || format!("path elem (layer {})", layer),
                    self.config.b_col,
                    row_offset,
                    || Ok(path_elem),
                )?;

                let _c_bit_cell = region.assign_advice(
                    || format!("challenge bit (layer {})", layer),
                    self.config.c_col,
                    row_offset,
                    || Ok(c_bit),
                )?;

                // Expose the challenge bit as a public input.
                self.config.s_pub.enable(&mut region, row_offset)?;

                // Boolean constrain the challenge bit.
                self.config.s_bool.enable(&mut region, row_offset)?;

                // Enable the "swap" gate to ensure the correct order of the Merkle hash inputs.
                self.config.s_swap.enable(&mut region, row_offset)?;

                // In the next row, allocate the correctly ordered Merkle hash inputs, calculated digest, and
                // enable the "hash" gate. If this is the last tree layer, expose the calculated
                // digest as a public input for the tree's root.
                row_offset += 1;

                let (preimg_l_value, preimg_r_value): (Fp, Fp) = if c_bit == Fp::zero() {
                    (a_value, path_elem)
                } else {
                    (path_elem, a_value)
                };

                let _preimg_l_cell = region.assign_advice(
                    || format!("preimg_l (layer {})", layer),
                    self.config.a_col,
                    row_offset,
                    || Ok(preimg_l_value),
                )?;

                let _preimg_r_cell = region.assign_advice(
                    || format!("preimage right (layer {})", layer),
                    self.config.b_col,
                    row_offset,
                    || Ok(preimg_r_value),
                )?;

                let digest_value = mock_hash(preimg_l_value, preimg_r_value);

                let digest_cell = region.assign_advice(
                    || format!("digest (layer {})", layer),
                    self.config.c_col,
                    row_offset,
                    || Ok(digest_value),
                )?;

                digest_alloc = Some(Alloc {
                    cell: digest_cell,
                    value: digest_value,
                });

                self.config.s_hash.enable(&mut region, row_offset)?;

                // If the calculated digest is the tree's root, expose it as a public input.
                let digest_is_root = layer == PATH_LEN - 1;
                if digest_is_root {
                    self.config.s_pub.enable(&mut region, row_offset)?;
                }

                Ok(())
            }
        )?;

        Ok(digest_alloc.unwrap())
    }
}

#[derive(Clone)]
struct MerkleCircuit {
    // Private inputs.
    leaf: Option<Fp>,
    path: Option<Vec<Fp>>,
    // Public inputs (from the prover). The root is also a public input, but it is calculated within
    // the circuit.
    c_bits: Option<Vec<Fp>>,
}

impl Circuit<Fp> for MerkleCircuit {
    type Config = MerkleChipConfig;

    fn configure(cs: &mut ConstraintSystem<Fp>) -> Self::Config {
        MerkleChip::configure(cs)
    }

    fn synthesize(&self, cs: &mut impl Assignment<Fp>, config: Self::Config) -> Result<(), Error> {
        let mut layouter = SingleChipLayouter::new(cs)?;
        let merkle_chip = MerkleChip::new(config);
        let mut layer_digest = merkle_chip.hash_leaf_layer(
            &mut layouter,
            self.leaf.as_ref().unwrap().clone(),
            self.path.as_ref().unwrap()[0],
            self.c_bits.as_ref().unwrap()[0].clone(),
        )?;
        for layer in 1..PATH_LEN {
            layer_digest = merkle_chip.hash_non_leaf_layer(
                &mut layouter,
                layer_digest,
                self.path.as_ref().unwrap()[layer].clone(),
                self.c_bits.as_ref().unwrap()[layer].clone(),
                layer,
            )?;
        }
        Ok(())
    }
}

struct Tree(Vec<Vec<Fp>>);

impl Tree {
    fn rand() -> Self {
        let mut rng = thread_rng();
        let leafs: Vec<Fp> = (0..N_LEAFS).map(|_| Fp::random(&mut rng)).collect();
        let mut layers = vec![leafs];
        for l in 1..TREE_LAYERS {
            let layer: Vec<Fp> = layers[l - 1]
                .chunks(2)
                .map(|pair| mock_hash(pair[0], pair[1]))
                .collect();
            layers.push(layer)
        }
        assert_eq!(layers.last().unwrap().len(), 1);
        Tree(layers)
    }

    fn root(&self) -> Fp {
        self.0.last().unwrap()[0]
    }

    fn leafs(&self) -> &[Fp] {
        self.0.first().unwrap()
    }

    fn gen_path(&self, c: usize) -> Vec<Fp> {
        let mut path = vec![];
        let mut node_index = c;
        for layer in 0..PATH_LEN {
            let sib = if node_index & 1 == 0 {
                self.0[layer][node_index + 1].clone()
            } else {
                self.0[layer][node_index - 1].clone()
            };
            path.push(sib);
            node_index /= 2;
        }
        path
    }
}

fn main() {
    assert!(N_LEAFS.is_power_of_two());

    // Generate a Merkle tree from random data.
    let tree = Tree::rand();

    // Generate a random challenge, i.e. a leaf index in `[0, N_LEAFS)`.
    let c: usize = thread_rng().gen_range(0..N_LEAFS);
    let c_bits: Vec<Fp> = (0..PATH_LEN)
        .map(|i| {
            if (c >> i) & 1 == 0 {
                Fp::zero()
            } else {
                Fp::one()
            }
        })
        .collect();

    // Create the public inputs. Every other row in the constraint system has a public input for a
    // challenge bit, additionally the last row has a public input for the root.
    let k = (N_ROWS_USED as f32).log2().ceil() as u32;
    let mut pub_inputs = vec![Fp::zero(); 1 << k];
    for i in 0..PATH_LEN {
        pub_inputs[2 * i] = c_bits[i].clone();
    }
    pub_inputs[LAST_ROW] = tree.root();

    // Assert that the constraint system is satisfied for a witness corresponding to `pub_inputs`.
    let circuit = MerkleCircuit {
        leaf: Some(tree.leafs()[c].clone()),
        path: Some(tree.gen_path(c)),
        c_bits: Some(c_bits),
    };
    let prover = MockProver::run(k, &circuit, vec![pub_inputs.clone()]).unwrap();
    assert!(prover.verify().is_ok());

    // Assert that changing the public challenge causes the constraint system to become unsatisfied.
    let mut bad_pub_inputs = pub_inputs.clone();
    bad_pub_inputs[0] = if pub_inputs[0] == Fp::zero() {
        Fp::one()
    } else {
        Fp::zero()
    };
    let prover = MockProver::run(k, &circuit, vec![bad_pub_inputs]).unwrap();
    let res = prover.verify();
    assert!(res.is_err());
    if let Err(errors) = res {
        assert_eq!(errors.len(), 1);
        if let VerifyFailure::Gate { gate_name, row, .. } = errors[0] {
            assert_eq!(gate_name, "public input");
            assert_eq!(row, 0);
        } else {
            panic!("expected public input gate failure");
        }
    }

    // Assert that changing the public root causes the constraint system to become unsatisfied.
    let mut bad_pub_inputs = pub_inputs.clone();
    bad_pub_inputs[LAST_ROW] += Fp::one();
    let prover = MockProver::run(k, &circuit, vec![bad_pub_inputs]).unwrap();
    let res = prover.verify();
    assert!(res.is_err());
    if let Err(errors) = res {
        assert_eq!(errors.len(), 1);
        if let VerifyFailure::Gate { gate_name, row, .. } = errors[0] {
            assert_eq!(gate_name, "public input");
            assert_eq!(row, LAST_ROW);
        } else {
            panic!("expected public input gate failure");
        }
    }

    // Assert that a non-boolean challenge bit causes the boolean constrain and swap gates to fail.
    let mut bad_pub_inputs = pub_inputs.clone();
    bad_pub_inputs[0] = Fp::from(2);
    let mut bad_circuit = circuit.clone();
    bad_circuit.c_bits.as_mut().unwrap()[0] = Fp::from(2);
    let prover = MockProver::run(k, &bad_circuit, vec![bad_pub_inputs]).unwrap();
    let res = prover.verify();
    assert!(res.is_err());
    if let Err(errors) = res {
        assert_eq!(errors.len(), 2);
        if let VerifyFailure::Gate { gate_name, row, .. } = errors[0] {
            assert_eq!(gate_name, "boolean constrain");
            assert_eq!(row, 0);
        } else {
            panic!("expected boolean constrain gate failure");
        }
        if let VerifyFailure::Gate { gate_name, row, .. } = errors[1] {
            assert_eq!(gate_name, "swap");
            assert_eq!(row, 0);
        } else {
            panic!("expected swap gate failure");
        }
    }

    // Assert that changing the witnessed path causes the constraint system to become unsatisfied
    // when checking that the calculated root is equal to the public input root.
    let mut bad_circuit = circuit.clone();
    bad_circuit.path.as_mut().unwrap()[0] += Fp::one();
    let prover = MockProver::run(k, &bad_circuit, vec![pub_inputs.clone()]).unwrap();
    let res = prover.verify();
    assert!(res.is_err());
    if let Err(errors) = res {
        assert_eq!(errors.len(), 1);
        if let VerifyFailure::Gate { gate_name, row, .. } = errors[0] {
            assert_eq!(gate_name, "public input");
            assert_eq!(row, LAST_ROW);
        } else {
            panic!("expected public input gate failure");
        }
    }
}
