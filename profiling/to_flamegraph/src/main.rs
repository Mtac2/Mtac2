extern crate sequence_trie;

use std::io;
use std::cell::{Cell};
use std::io::{BufRead, Write};

use sequence_trie::*;

mod stacks;

fn main() -> () {
    let s = std::io::stdin();
    let locked = s.lock();

    let mut trie : SequenceTrie<String, f64> = SequenceTrie::new();

    let p = stacks::LineParser::new();
    for line in locked.lines() {
        let l = line.expect("???");
        let (stacks, time) = p.parse(&l).expect("misformed");

        if stacks.len() > 1 {
            let parent = &stacks[0..stacks.len()-1];
            let insert =
                match trie.get_mut(parent) {
                    None => true,
                    Some(mut v) => { (*v -= time); false },
                };
            if insert {
                trie.insert(parent, 0.0-time);
            }
        }

        let node = &stacks[..];
        let insert =
            match trie.get_mut(node) {
                None => true,
                Some(mut v) => { (*v += time); false },
            };
        if insert {
            trie.insert(node, time);
        }
    }

    let s = std::io::stdout();
    let mut locked = s.lock();
    for (mut k,v) in trie.iter() {
        let v = if f64::abs(*v) < 1e-6 { 0.0 } else { *v };
        let mut last = k.pop().unwrap();
        for s in k {
            locked.write(s.as_str().as_bytes()).expect("??");
            locked.write(";".as_bytes()).expect("???");
        }
        locked.write(last.as_str().as_bytes()).expect("????");
        locked.write(" ".as_bytes()).expect("?????");
        write!(locked, "{}\n", v).expect("??????");
    }
}
