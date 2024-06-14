use std::collections::{HashMap, HashSet};
use sha2::{Sha256, Digest};
use serde::{Deserialize, Serialize};

pub const HASH_LEN: usize = 32;
pub const HASH_LEN_BITS: u16 = HASH_LEN as u16 * 8;

pub type Hash = [u8; HASH_LEN];
pub type ID = Hash;
pub type ValueHash = Hash;
pub type NodeIDHash = Hash;

pub type DefaultHasher = Sha256;
pub type ResultT<T> = Result<T, &'static str>;

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Leaf {
    id: ID,
    hash: ValueHash,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub enum Child {
    Leaf(Leaf),
    SubRoot(NodeIDHash),
}

impl Child {
    pub fn get_hash(&self) -> Hash {
        match &self {
            Child::Leaf(leaf) => { leaf.hash }
            Child::SubRoot(sr) => { *sr }
        }
    }
}

// also return if a is the left
pub fn common_prefix_len(a: &ID, b: &ID) -> (u16, bool) {
    let cp_bytes = a.iter().zip(b).take_while(|(&x, &y)| x == y).count();
    let mut cpl = 8u16 * (cp_bytes as u16);
    let mut a_is_left = true;
    if cpl == 256u16 {
        return (cpl, a_is_left);
    }

    let a = a[cp_bytes];
    let b = b[cp_bytes];
    //println!("common_prefix_len: {:b}, {:b}", a, b);
    let mut mask = 1u8 << 7;
    for _ in 0usize..HASH_LEN {
        let a_bit = a & mask;
        let b_bit = b & mask;
        if a_bit == b_bit {
            cpl += 1;
            mask = mask >> 1;
        } else {
            a_is_left = a_bit == 0;
        }
    }
    (cpl, a_is_left)
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Inner {
    r_id: ID,
    cp_len: u16,
    l_dirty: bool,
    r_dirty: bool,
    l: Child,
    r: Child,
}

impl Inner {
    pub fn new_one(a_id: ID, a: ValueHash) -> Inner {
        let b_id = ID::default();
        let b = Child::SubRoot(NodeIDHash::default());
        Self::new(a_id, a, b_id, b)
    }

    pub fn new(a_id: ID, a: ValueHash, b_id: ID, b: Child) -> Inner {
        let a = Child::Leaf(Leaf { id: a_id, hash: a });
        let (cp_len, a_is_left) = common_prefix_len(&a_id, &b_id);
        let (l, r) = if a_is_left { (a, b) } else { (b, a) };
        Inner {
            r_id: if a_is_left { b_id } else { a_id },
            cp_len,
            l_dirty: false,
            r_dirty: false,
            l,
            r,
        }
    }

    pub fn hash(&self) -> Hash {
        let mut hasher = DefaultHasher::new();
        hasher.update(self.l.get_hash());
        hasher.update(self.r.get_hash());
        hasher.finalize().as_slice().try_into().expect("Hash")
    }
}
//
// fn hash_of_default_hash() -> Hash {
//     let mut hasher = DefaultHasher::new();
//     hasher.update(Hash::default());
//     hasher.finalize().as_slice().try_into().expect("Hash")
// }

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Proof {
    // root : NodeIDHash,
    v_hash: ValueHash,
    path: Vec<(bool, NodeIDHash)>,
}

impl Proof {
    pub fn verify(&self, root: &Hash) -> bool {
        let r = self.path.iter().rev().fold(self.v_hash, |round_hash, (left, ph)| {
            let mut hasher = DefaultHasher::new();
            let (a, b) = if *left { (ph, &round_hash) } else { (&round_hash, ph) };
            hasher.update(a);
            hasher.update(b);
            hasher.finalize().as_slice().try_into().expect("Hash")
        });
        r == *root
    }
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct PartialMerkleTrie {
    pub root: Hash,
    pub root_dirty: bool,
    pub leaf_count: usize,
    //try BTreeMap
    pub inner_store: HashMap<Hash, Inner>,
}

impl PartialMerkleTrie {
    pub fn new() -> PartialMerkleTrie {
        PartialMerkleTrie {
            root: Hash::default(),
            root_dirty: false,
            leaf_count: 0,
            inner_store: HashMap::new(),
        }
    }

    fn update_sub_root(&mut self, node_id: NodeIDHash) -> NodeIDHash {
        let mut node = self.inner_store.remove(&node_id).expect("node not exist");
        if node.l_dirty {
            match node.l {
                Child::Leaf(_) => { panic!("leaf cannot be dirty") }
                Child::SubRoot(next_hash) => {
                    let new_hash = self.update_sub_root(next_hash);
                    node.l = Child::SubRoot(new_hash);
                }
            };
            node.l_dirty = false;
        }

        if node.r_dirty {
            match node.r {
                Child::Leaf(_) => { panic!("leaf cannot be dirty") }
                Child::SubRoot(next_hash) => {
                    let new_hash = self.update_sub_root(next_hash);
                    node.r = Child::SubRoot(new_hash);
                }
            };
            node.r_dirty = false;
        }

        let h = node.hash();
        self.inner_store.insert(h, node);
        h
    }

    fn update_root(&mut self) {
        self.root = self.update_sub_root(self.root);
        self.root_dirty = false;
    }

    pub fn get(&self, id: &ID) -> Option<ValueHash> {
        match self.leaf_count
        {
            n if n == 0 => {}
            n if n == 1 => {
                let node = self.inner_store.get(&self.root).expect("node not exist");
                match &node.r {
                    Child::Leaf(l) => {
                        if l.id == *id {
                            return Some(l.hash);
                        }
                    }
                    Child::SubRoot(_) => { panic!("subtree should not exist") }
                }
            }
            _ => {
                let mut cur_node_id = &self.root;
                loop {
                    let current = self.inner_store.get(cur_node_id).expect("node not exist");
                    let (cp_len, a_is_left) = common_prefix_len(&id, &current.r_id);
                    match cp_len {
                        n if n < current.cp_len => {
                            break;
                        }
                        n if n == current.cp_len && a_is_left => {
                            match &current.l {
                                Child::Leaf(l) => {
                                    if *id == l.id {
                                        return Some(l.hash);
                                    }
                                    break;
                                }
                                Child::SubRoot(sr) => {
                                    cur_node_id = sr;
                                }
                            }
                        }
                        _ => {
                            match &current.r {
                                Child::Leaf(l) => {
                                    if *id == l.id {
                                        return Some(l.hash);
                                    }
                                    break;
                                }
                                Child::SubRoot(sr) => {
                                    cur_node_id = sr;
                                }
                            }
                        }
                    }
                }
            }
        }
        None
    }

    pub fn get_proof(&self, id: &ID) -> Option<Proof> {
        match self.leaf_count
        {
            n if n == 0 => {}
            n if n == 1 => {
                let node = self.inner_store.get(&self.root).expect("node not exist");
                match &node.r {
                    Child::Leaf(l) => {
                        if l.id == *id {
                            return Some(Proof {
                                // root: self.root,
                                v_hash: l.hash,
                                path: vec![(true, NodeIDHash::default())],
                            });
                        }
                    }
                    Child::SubRoot(_) => { panic!("subtree should not exist") }
                }
            }
            _ => {
                let mut cur_node_id = &self.root;
                let mut path = vec![];
                loop {
                    let current = self.inner_store.get(cur_node_id).expect("node not exist");
                    let (cp_len, a_is_left) = common_prefix_len(&id, &current.r_id);
                    match cp_len {
                        n if n < current.cp_len => {
                            break;
                        }
                        n if n == current.cp_len && a_is_left => {
                            path.push((false, current.r.get_hash()));
                            match &current.l {
                                Child::Leaf(leaf) => {
                                    if *id == leaf.id {
                                        return Some(Proof {
                                            // root: self.root,
                                            v_hash: leaf.hash,
                                            path,
                                        });
                                    }
                                    break;
                                }
                                Child::SubRoot(sr) => {
                                    cur_node_id = sr;
                                }
                            }
                        }
                        _ => {
                            path.push((true, current.l.get_hash()));
                            match &current.r {
                                Child::Leaf(leaf) => {
                                    if *id == leaf.id {
                                        return Some(Proof {
                                            // root: self.root,
                                            v_hash: leaf.hash,
                                            path,
                                        });
                                    }
                                    break;
                                }
                                Child::SubRoot(sr) => {
                                    cur_node_id = sr;
                                }
                            }
                        }
                    }
                }
            }
        }
        return None;
    }

    pub fn get_partial(&self, ids: &Vec<&ID>) -> PartialMerkleTrie {
        assert!(!self.root_dirty);
        let mut partial = PartialMerkleTrie {
            root: self.root,
            root_dirty: false,
            leaf_count: self.leaf_count,
            inner_store: Default::default(),
        };

        if self.leaf_count <= 2 {
            partial.inner_store = self.inner_store.clone();
            return partial;
        }

        for &id in ids {
            let mut cur_node_id = &self.root;
            loop {
                let current = if !partial.inner_store.contains_key(cur_node_id) {
                    let node = self.inner_store.get(cur_node_id).expect("no root");
                    partial.inner_store.insert(*cur_node_id, node.clone());
                    node
                } else {
                    partial.inner_store.get(cur_node_id).unwrap()
                };

                let (cp_len, a_is_left) = common_prefix_len(&id, &current.r_id);
                match cp_len {
                    n if n < current.cp_len => {
                        break;
                    }
                    n if n == current.cp_len && a_is_left => {
                        match &current.l {
                            Child::Leaf(_) => {
                                break;
                            }
                            Child::SubRoot(sr) => {
                                cur_node_id = sr;
                            }
                        }
                    }
                    _ => {
                        match &current.r {
                            Child::Leaf(_) => {
                                break;
                            }
                            Child::SubRoot(sr) => {
                                cur_node_id = sr;
                            }
                        }
                    }
                }
            }
        }

        partial
    }

    pub fn verify_partial(&self) -> bool {
        match self.leaf_count {
            n if n == 0 => {
                return self.root == Hash::default() && self.inner_store.len() == 0;
            }
            n if n <= 2 => {
                let inner = self.inner_store.get(&self.root);
                match inner {
                    None => {
                        return false;
                    }
                    Some(i) => {
                        match &i.l {
                            Child::Leaf(_) => {}
                            Child::SubRoot(_) => {
                                return false;
                            }
                        }
                        match &i.r {
                            Child::Leaf(_) => {}
                            Child::SubRoot(_) => {
                                return false;
                            }
                        }
                        if !(self.inner_store.len() == 1 && i.hash() == self.root) {
                            return false;
                        }
                    }
                }
                return true;
            }
            _ => {
                let mut node_ids = HashSet::new();
                let good = self.verify_partial_rec(&self.root, &mut node_ids);
                good && self.inner_store.len() == node_ids.len()
            }
        }
    }

    pub fn verify_partial_rec(&self, cur_node_id: &NodeIDHash, node_ids: &mut HashSet<NodeIDHash>) -> bool
    {
        let current_op = self.inner_store.get(cur_node_id);
        match current_op {
            None => { return true; }
            Some(current) => {
                node_ids.insert(*cur_node_id);
                if *cur_node_id != current.hash() {
                    // println!("bad node s {:?}", cur_node_id);
                    return false;
                }
                match &current.l {
                    Child::Leaf(_) => {}
                    Child::SubRoot(sr) => {
                        if !self.verify_partial_rec(sr, node_ids) {
                            // println!("bad node l {:?}", cur_node_id);
                            return false;
                        }
                    }
                }
                match &current.r {
                    Child::Leaf(_) => {}
                    Child::SubRoot(sr) => {
                        if !self.verify_partial_rec(sr, node_ids) {
                            // println!("bad node r {:?}", cur_node_id);
                            return false;
                        }
                    }
                }
                // println!("good node  {:?}", cur_node_id);

                true
            }
        }
    }

    pub fn insert_or_replace(&mut self, a_id: ID, a_hash: Hash) {
        self.insert_or_replace_internal(a_id, a_hash);
        if self.root_dirty {
            self.update_root();
        }
    }

    pub fn insert_or_replace_batch(&mut self, items: Vec<(ID, Hash)>) {
        for (a_id, a_hash) in items {
            // println!("bt insert new pair {:?} {:?}", a_id, a_hash);
            self.insert_or_replace_internal(a_id, a_hash);
        }

        if self.root_dirty {
            // println!("bt update root b   {:?}", self.root);
            self.update_root();
            // println!("bt update root a   {:?}", self.root);
        }
    }

    pub fn insert_or_replace_internal(&mut self, a_id: ID, a_hash: Hash) {
        match self.leaf_count {
            n if n == 0 => {
                let node = Inner::new_one(a_id, a_hash);
                self.root = node.hash();
                self.leaf_count = 1;
                // println!("rf insert new node {:?}", self.root);
                self.inner_store.insert(self.root, node);
            }
            n if n == 1 => {
                let mut node = self.inner_store.remove(&self.root).expect("root not exist");
                if a_id == node.r_id//TODO double check when adding remove()
                {
                    node = Inner::new_one(a_id, a_hash);
                } else {
                    node = Inner::new(a_id, a_hash, node.r_id, node.r);
                    self.leaf_count = 2;
                }
                self.root = node.hash();
                // println!("rs insert new node {:?}", self.root);
                self.inner_store.insert(self.root, node);
            }
            _ => {
                let new_root = self.insert_or_replace_rec(a_id, a_hash, self.root, self.root_dirty);
                if new_root.is_some() {
                    self.root = new_root.unwrap();
                } else {
                    // println!("need update        {:?}", a_id);
                    self.root_dirty = true;
                }
            }
        }
    }

    fn insert_or_replace_rec(&mut self, a_id: ID, a_hash: Hash, cur_node_id: NodeIDHash, is_root_and_dirty: bool) -> Option<NodeIDHash> {
        let current = self.inner_store.get_mut(&cur_node_id).expect("node not exist");
        let (cp_len, a_is_left) = common_prefix_len(&a_id, &current.r_id);
        let next_step = match cp_len {
            n if n < current.cp_len => {
                let mut new_node = Inner::new(a_id, a_hash, current.r_id, Child::SubRoot(cur_node_id));
                if current.l_dirty || current.r_dirty || is_root_and_dirty { // child dirty
                    if a_is_left {
                        new_node.r_dirty = true;
                    } else {
                        new_node.l_dirty = true;
                    }
                }
                let new_hash = new_node.hash();
                // println!("up insert new node {:?}", new_hash);
                self.inner_store.insert(new_hash, new_node);
                self.leaf_count += 1;
                return Some(new_hash);
            }
            n if n == current.cp_len && a_is_left => {
                match &mut current.l {
                    Child::Leaf(leaf) => {
                        if a_id == leaf.id {
                            leaf.hash = a_hash;
                        } else {
                            let new_node = Inner::new(a_id, a_hash, leaf.id, Child::Leaf(leaf.clone()));
                            let new_hash = new_node.hash();
                            (*current).l = Child::SubRoot(new_hash);
                            // println!("le insert new node {:?}", new_hash);
                            self.inner_store.insert(new_hash, new_node);
                            self.leaf_count += 1;
                        }
                        None
                    }
                    Child::SubRoot(sr) => {
                        current.l_dirty = true;
                        Some((*sr, true))
                    }
                }
            }
            _ => {
                match &mut current.r {
                    Child::Leaf(leaf) => {
                        if a_id == leaf.id {
                            leaf.hash = a_hash;
                        } else {
                            let new_node = Inner::new(a_id, a_hash, leaf.id, Child::Leaf(leaf.clone()));
                            let new_hash = new_node.hash();
                            (*current).r = Child::SubRoot(new_hash);
                            // println!("ri insert new node {:?}", new_hash);
                            self.inner_store.insert(new_hash, new_node);
                            self.leaf_count += 1;
                        }
                        None
                    }
                    Child::SubRoot(sr) => {
                        current.r_dirty = true;
                        Some((*sr, false))
                    }
                }
            }
        };

        if next_step.is_some() {
            let (next_hash, go_left) = next_step.unwrap();
            let update = self.insert_or_replace_rec(a_id, a_hash, next_hash, false);
            if update.is_some() {
                let current = self.inner_store.get_mut(&cur_node_id).expect("node not exist");
                let to_reset = if go_left { &mut current.l_dirty } else { &mut current.r_dirty };
                assert!(*to_reset);
                *to_reset = false;

                let kid = if go_left { &mut current.l } else { &mut current.r };
                match kid {
                    Child::Leaf(_) => { panic!("wrong child type") }
                    Child::SubRoot(sr) => {
                        *sr = update.unwrap();
                    }
                }
            }
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn create_key_value(first_byte: u8) -> (ID, Hash) {
        let mut id = Hash::default();
        id[0] = first_byte;
        let mut vh = Hash::default();
        vh[1] = 255;
        vh[2] = first_byte;
        (id, vh)
    }

    #[test]
    fn common_prefix_len_works() {
        let de = Hash::default();
        assert_eq!((256, true), common_prefix_len(&de, &de));
        let mut a = de;
        a[3] = 32u8;
        assert_eq!((2 + 24, false), common_prefix_len(&a, &de));
        a[4] = 32u8;
        assert_eq!((2 + 24, false), common_prefix_len(&a, &de));
        a[0] = 255u8;
        assert_eq!((0, false), common_prefix_len(&a, &de));
        a[0] = 32u8;
        assert_eq!((2, false), common_prefix_len(&a, &de));
        assert_eq!((2, true), common_prefix_len(&de, &a));

        // println!("{:?}", common_prefix_len(&a, &de));
    }

    #[allow(dead_code)]
    #[test]
    fn trie_works() {
        let mut temp = Hash::default();
        temp[4] = 255;
        let (k_1, v_1) = create_key_value(1);
        let (k_2, v_2) = create_key_value(2);
        let (k_3, v_3) = create_key_value(3);
        let (k_32, v_32) = create_key_value(32);//
        let (k_64, v_64) = create_key_value(64);
        let (k_85, v_85) = create_key_value(85);//
        let (k_128, v_128) = create_key_value(128);
        let (k_130, v_130) = create_key_value(130);//
        let (k_200, v_200) = create_key_value(200);//
        let (k_254, v_254) = create_key_value(254);
        let (k_255, v_255) = create_key_value(255);

        // single inserts
        let mut tr = PartialMerkleTrie::new();
        {
            {
                // println!("ri insert key      255");
                tr.insert_or_replace(k_255, temp);//need clone?
                // println!("root               {:?}", tr.root);
                // println!("ri insert key      255");
                tr.insert_or_replace(k_255, v_255);
                assert_eq!(tr.leaf_count, 1);
                assert_eq!(tr.inner_store.len(), 1);
                // println!("root               {:?}", tr.root);
                // println!("ri insert key      254");
                tr.insert_or_replace(k_254, temp);
                // println!("root               {:?}", tr.root);
                // println!("ri insert key      254");
                tr.insert_or_replace(k_254, v_254);
                assert_eq!(tr.leaf_count, 2);
                assert_eq!(tr.inner_store.len(), 1);
                // println!("root               {:?}", tr.root);
                // println!("ri insert key      1");
                tr.insert_or_replace(k_1, temp);
                // println!("root               {:?}", tr.root);
                // println!("ri insert key      1");
                tr.insert_or_replace(k_1, v_1);
                assert_eq!(tr.leaf_count, 3);
                assert_eq!(tr.inner_store.len(), 2);
                // println!("root               {:?}", tr.root);
                // println!("ri insert key      2");
                tr.insert_or_replace(k_2, temp);
                // println!("root               {:?}", tr.root);
                // println!("ri insert key      2");
                tr.insert_or_replace(k_2, v_2);
                assert_eq!(tr.leaf_count, 4);
                assert_eq!(tr.inner_store.len(), 3);
                // println!("root               {:?}", tr.root);
                // println!("ri insert key      128");
                tr.insert_or_replace(k_128, temp);
                // println!("root               {:?}", tr.root);
                // println!("ri insert key      128");
                tr.insert_or_replace(k_128, v_128);
                assert_eq!(tr.leaf_count, 5);
                assert_eq!(tr.inner_store.len(), 4);
                // println!("root               {:?}", tr.root);
                // println!("ri insert key      64");
                tr.insert_or_replace(k_64, temp);
                // println!("root               {:?}", tr.root);
                // println!("ri insert key      64");
                tr.insert_or_replace(k_64, v_64);
                assert_eq!(tr.leaf_count, 6);
                assert_eq!(tr.inner_store.len(), 5);
                // println!("root               {:?}", tr.root);
                // println!("ri insert key      3");
                tr.insert_or_replace(k_3, temp);
                // println!("root               {:?}", tr.root);
                // println!("ri insert key      3");
                tr.insert_or_replace(k_3, v_3);
                // println!("root               {:?}", tr.root);
                assert_eq!(tr.leaf_count, 7);
                assert_eq!(tr.inner_store.len(), 6);
            }

            {
                let mut td = PartialMerkleTrie::new();
                td.insert_or_replace(k_1, temp);
                td.insert_or_replace(k_1, v_1);
                td.insert_or_replace(k_2, temp);
                td.insert_or_replace(k_2, v_2);
                td.insert_or_replace(k_3, temp);
                td.insert_or_replace(k_3, v_3);
                td.insert_or_replace(k_64, temp);
                td.insert_or_replace(k_64, v_64);
                td.insert_or_replace(k_128, temp);
                td.insert_or_replace(k_128, v_128);
                td.insert_or_replace(k_254, temp);
                td.insert_or_replace(k_254, v_254);
                td.insert_or_replace(k_255, temp);
                td.insert_or_replace(k_255, v_255);
                assert_eq!(td.leaf_count, 7);
                assert_eq!(td.inner_store.len(), 6);
                assert_eq!(tr.root, td.root);
            }

            {
                let mut td = PartialMerkleTrie::new();
                td.insert_or_replace(k_255, temp);
                td.insert_or_replace(k_255, v_255);
                td.insert_or_replace(k_254, temp);
                td.insert_or_replace(k_254, v_254);
                td.insert_or_replace(k_128, temp);
                td.insert_or_replace(k_128, v_128);
                td.insert_or_replace(k_64, temp);
                td.insert_or_replace(k_64, v_64);
                td.insert_or_replace(k_3, temp);
                td.insert_or_replace(k_3, v_3);
                td.insert_or_replace(k_2, temp);
                td.insert_or_replace(k_2, v_2);
                td.insert_or_replace(k_1, temp);
                td.insert_or_replace(k_1, v_1);
                assert_eq!(td.leaf_count, 7);
                assert_eq!(td.inner_store.len(), 6);
                assert_eq!(tr.root, td.root);
            }
        }

        // batch inserts
        {
            {
                let items: Vec<(ID, Hash)> = vec![
                    (k_1, v_1), (k_2, v_2), (k_3, v_3), (k_64, v_64),
                    (k_128, v_128), (k_254, v_254), (k_255, v_255),
                ];
                let mut td = PartialMerkleTrie::new();
                td.insert_or_replace_batch(items);
                assert_eq!(td.leaf_count, 7);
                assert_eq!(td.inner_store.len(), 6);
                // println!("tr root            {:?}", tr.root);
                // println!("td root            {:?}", td.root);
                assert_eq!(tr.root, td.root);
            }

            {
                let items: Vec<(ID, Hash)> = vec![
                    (k_255, v_255), (k_254, v_254), (k_128, v_128),
                    (k_64, v_64), (k_3, v_3), (k_2, v_2), (k_1, v_1),
                ];
                let mut td = PartialMerkleTrie::new();
                td.insert_or_replace_batch(items);
                assert_eq!(td.leaf_count, 7);
                assert_eq!(td.inner_store.len(), 6);
                // println!("tr root            {:?}", tr.root);
                // println!("td root            {:?}", td.root);
                assert_eq!(tr.root, td.root);
            }
        }

        // partial trie
        {
            let ids = vec![&k_1, &k_2, &k_3, &k_64, &k_128, &k_254, &k_255];
            let tp = tr.get_partial(&ids);
            assert_eq!(tp.inner_store.len(), 6);
            assert!(tp.verify_partial());

            let ids = vec![&k_255, &k_254, &k_128, &k_64, &k_3, &k_2, &k_1];
            let tp = tr.get_partial(&ids);
            assert_eq!(tp.inner_store.len(), 6);
            assert!(tp.verify_partial());

            let ids = vec![&k_64];
            let tp = tr.get_partial(&ids);
            assert_eq!(tp.inner_store.len(), 2);
            assert!(tp.verify_partial());

            let ids = vec![];
            let tp = tr.get_partial(&ids);
            assert_eq!(tp.inner_store.len(), 0);
            assert!(tp.verify_partial());

            let ids = vec![&k_32];
            let mut tp = tr.get_partial(&ids);
            assert_eq!(tp.inner_store.len(), 3);
            assert!(tp.verify_partial());
            tr.insert_or_replace(k_32, v_32);//need clone?
            tp.insert_or_replace(k_32, v_32);
            assert_eq!(tp.root, tr.root);
            assert!(tp.verify_partial());

            let ids = vec![&k_85, &k_130, &k_200];
            let mut tp = tr.get_partial(&ids);
            assert_eq!(tp.inner_store.len(), 4);
            assert!(tp.verify_partial());

            tr.insert_or_replace(k_85, v_85);
            tr.insert_or_replace(k_130, v_130);
            tr.insert_or_replace(k_200, v_200);
            tp.insert_or_replace_batch(vec![(k_85, v_85), (k_130, v_130), (k_200, v_200)]);

            assert_eq!(tp.root, tr.root);
            assert_eq!(tp.leaf_count, 11);
            assert_eq!(tr.leaf_count, 11);
            assert!(tp.verify_partial());

            tp.inner_store.insert(Hash::default(), Inner::new_one(Hash::default(), Hash::default()));
            assert!(!tp.verify_partial());
        }

        // Merkle proof
        {
            {
                let id = Hash::default();
                assert!(tr.get_proof(&id).is_none());
                let ids = vec![&k_1, &k_2, &k_3, &k_32, &k_64, &k_85, &k_128, &k_130, &k_200, &k_254, &k_255];
                for &id in &ids {
                    let p = tr.get_proof(id).unwrap();
                    assert!(p.verify(&tr.root));
                }
                for &id in &ids {
                    let p = tr.get_proof(id).unwrap();
                    assert!(p.verify(&tr.root));
                }
            }
            {
                let mut td = PartialMerkleTrie::new();
                td.insert_or_replace(k_1, v_1);
                assert!(td.get_proof(&k_1).unwrap().verify(&td.root));
                td.insert_or_replace(k_2, v_2);
                assert!(td.get_proof(&k_2).unwrap().verify(&td.root));
                td.insert_or_replace(k_3, v_3);
                assert!(td.get_proof(&k_3).unwrap().verify(&td.root));
            }
        }

        // get
        {
            {
                let items: Vec<(ID, Hash)> = vec![
                    (k_1, v_1), (k_2, v_2), (k_3, v_3), (k_32, v_32), (k_64, v_64), (k_85, v_85),
                    (k_128, v_128), (k_130, v_130), (k_200, v_200), (k_254, v_254), (k_255, v_255),
                ];
                for (id, vh) in &items {
                    assert_eq!(tr.get(id).unwrap(), *vh);
                }
                for (id, vh) in &items {
                    assert_eq!(tr.get(id).unwrap(), *vh);
                }
            }
            {
                let mut td = PartialMerkleTrie::new();
                td.insert_or_replace(k_1, v_1);
                assert_eq!(td.get(&k_1).unwrap(), v_1);
                td.insert_or_replace(k_2, v_2);
                assert_eq!(td.get(&k_2).unwrap(), v_2);
                td.insert_or_replace(k_3, v_3);
                assert_eq!(td.get(&k_3).unwrap(), v_3);
            }
        }
    }
}
