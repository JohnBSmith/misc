
use std::collections::HashMap;
use std::iter::zip;
use std::hash::Hash;

pub fn cartesian_power<T: Clone>(a: &[T], n: usize,
    callback: &mut dyn FnMut(&[T])
) {
    let m = a.len();
    let mut stack: Vec<usize> = Vec::with_capacity(n);
    let mut k: usize = 0;
    let mut i = 0;
    let mut b: Vec<T> = (0..n).map(|_| a[0].clone()).collect();
    loop {
        if i == n {
            callback(&b);
        } else if k < m {
            b[i] = a[k].clone();
            stack.push(k);
            k = 0; i += 1;
            continue;
        }
        match stack.pop() {
            Some(value) => {i -= 1; k = value + 1;}
            _ => break
        }
    }
}

pub fn mappings<X: Clone + Eq + Hash, Y: Clone>(ax: &[X], ay: &[Y],
    callback: &mut dyn FnMut(&[Y], &HashMap<X, Y>))
{
    cartesian_power(ay, ax.len(), &mut |t| {
        let m = zip(ax, t).map(|(x, y)| (x.clone(), y.clone())).collect();
        callback(t, &m);
    });
}

pub fn combinations<T: Clone>(a: &[T], k: usize, cb: &mut dyn FnMut(&[T])) {
    if k == 0 {
        cb(&[]);
    } else if k == a.len() {
        cb(&a);
    } else {
        let mut buf: Vec<T> = Vec::with_capacity(k);
        combinations(&a[1..], k - 1, &mut |c| {
            buf.push(a[0].clone());
            buf.extend_from_slice(c);
            cb(&buf);
            buf.clear();
        });
        combinations(&a[1..], k, cb);
    }
}

pub fn power_set<T: Clone>(a: &[T], cb: &mut dyn FnMut(&[T])) {
    for k in 0..a.len() + 1 {
        combinations(a, k, cb);
    }
}

pub fn prod2<X: Clone, Y: Clone>(a: &[X], b: &[Y]) -> Vec<(X, Y)> {
    let mut acc = Vec::with_capacity(a.len()*b.len());
    for x in a {
        for y in b {acc.push((x.clone(), y.clone()));}
    }
    acc
}


