extern crate sequence_trie;

use std::io;
use std::cell::{Cell};
use std::io::{BufRead, Write};

use sequence_trie::*;

use std::string::String;

extern crate fnv;

use fnv::FnvHashMap;

fn main() -> () {
    let s = std::io::stdin();
    let locked = s.lock();

    let mut trie : SequenceTrie<String, f64, fnv::FnvBuildHasher> = SequenceTrie::default();

    let mut stack_vec = vec![];

    for line in locked.lines() {
        let l = line.expect("???");

        let pos = l.rfind(" ").expect("no space in input line.");
        let (stack_str, float_str) = l.split_at(pos);
        let stacks : &Vec<String> = {
            stack_vec.clear();
            for stack in stack_str.split(";") {
                stack_vec.push(String::from(stack))
            };
            &stack_vec
        };
        let (_, time) = float_str.split_at(1);
        let time = time.parse::<f64>().expect("not a valid floating point.");

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
