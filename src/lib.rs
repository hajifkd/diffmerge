use std::collections::HashMap;

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum EditOp {
    DeleteLine { orig_line: usize },
    InsertLine { orig_line: usize, mod_line: usize },
}

// レーベンシュタイン距離を深さ優先でグリーディに求める
// O((n + m) * d) see https://link.springer.com/article/10.1007/BF01840446
pub fn diff(src: &str, dst: &str) -> Vec<EditOp> {
    let src_splits: Vec<&str> = src.split('\n').collect();
    let dst_splits: Vec<&str> = dst.split('\n').collect();
    let n = src_splits.len();
    let m = dst_splits.len();
    let mut furthest_xs: Vec<Option<usize>> = vec![None; n + m + 1];
    let mut path = HashMap::new();

    fn offset(m: usize, i: isize) -> usize {
        (i + m as isize) as usize
    }

    'outer: for d in 0..=(n + m) {
        let di = d as isize;
        let kmin = std::cmp::max(-di, -(m as isize));
        let kmax = std::cmp::min(di, n as isize);
        for i in (di + kmin + 1) / 2.. {
            let k = -di + 2 * i;
            if k > kmax {
                break;
            }
            let (start_x, start_y) = if d == 0 {
                (0, 0)
            } else {
                let x = if k == kmin {
                    if let Some(x) = furthest_xs[offset(m, k + 1)] {
                        path.insert((x, k), (x, k + 1));
                        x
                    } else {
                        continue;
                    }
                } else if k == kmax {
                    if let Some(x) = furthest_xs[offset(m, k - 1)] {
                        path.insert((x + 1, k), (x, k - 1));
                        x + 1
                    } else {
                        continue;
                    }
                } else {
                    if let Some(x1) = furthest_xs[offset(m, k + 1)] {
                        if let Some(x2) = furthest_xs[offset(m, k - 1)] {
                            let x2 = x2 + 1;

                            if x1 > x2 {
                                path.insert((x1, k), (x1, k + 1));
                                x1
                            } else {
                                path.insert((x2, k), (x2 - 1, k - 1));
                                x2
                            }
                        } else {
                            continue;
                        }
                    } else {
                        continue;
                    }
                };
                (x, x as isize - k)
            };

            if start_x > n || start_y > m as isize || start_y < 0 {
                continue;
            }

            let start_y = start_y as usize;

            let (mut x, mut y) = (start_x, start_y);

            while x + 1 <= n && y + 1 <= m && src_splits[x] == dst_splits[y] {
                x += 1;
                y += 1;
            }

            furthest_xs[offset(m, k)] = Some(x);
            if x != start_x {
                path.insert((x, k), (start_x, k));
            }

            if x == n && y == m {
                break 'outer;
            }
        }
    }
    let mut result = vec![];
    let mut point = (n, n as isize - m as isize);

    while point != (0, 0) {
        let (x, k) = point;
        let (x_next, k_next) = path[&point];
        point = path[&point];

        if k == k_next {
            continue;
        }

        if x == x_next {
            result.push(EditOp::InsertLine {
                orig_line: x + 1,
                mod_line: (x as isize - k) as usize,
            })
        } else {
            result.push(EditOp::DeleteLine { orig_line: x })
        }
    }

    result
}

#[cfg(test)]
mod tests {
    extern crate rand;
    use crate::*;
    use rand::prelude::*;
    fn gen_rand_str_lines(line_max: usize) -> String {
        let alphabets: Vec<_> = (b'a'..=b'z').map(char::from).collect();
        (0..random::<usize>() % line_max)
            .map(|i| alphabets[random::<usize>() % alphabets.len()])
            .fold(String::new(), |mut acc, x| {
                if acc.is_empty() {
                    acc.push(x);
                } else {
                    acc.push('\n');
                    acc.push(x);
                }
                acc
            })
    }
    #[test]
    fn test_diff() {
        for _ in 0..100 {
            let src = gen_rand_str_lines(100);
            let dst = gen_rand_str_lines(100);
            let ops = diff(&src, &dst);
            let mut src_lines: Vec<_> = src.split('\n').collect();
            let dst_lines: Vec<_> = dst.split('\n').collect();

            for op in ops {
                match op {
                    EditOp::DeleteLine { orig_line } => {
                        src_lines.remove(orig_line - 1);
                    }
                    EditOp::InsertLine {
                        orig_line,
                        mod_line,
                    } => {
                        src_lines.insert(orig_line - 1, dst_lines[mod_line - 1]);
                    }
                }
            }

            assert_eq!(src_lines, dst_lines);
        }
    }
}
