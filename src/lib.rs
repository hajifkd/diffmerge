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
    let mut furthest_xs: Vec<Option<(usize, Vec<EditOp>)>> = vec![None; n + m + 1];

    fn offset(n: usize, m: usize, i: isize) -> usize {
        (i + m as isize + 1) as usize
    }

    'outer: for d in 0..=std::cmp::max(n, m) {
        let di = d as isize;
        let kmin = std::cmp::max(-di, -(m as isize));
        let kmax = std::cmp::min(di, n as isize);
        for i in 0.. {
            let k = kmin + 2 * i;
            if k > kmax {
                break;
            }

            let (start_x, start_y, op) = if d == 0 {
                (0, 0, vec![])
            } else {
                let (x, op) = if k == kmin {
                    let (x, mut op) = furthest_xs[offset(n, m, k + 1)].as_ref().unwrap().clone();
                    op.push(EditOp::InsertLine {
                        orig_line: x,
                        mod_line: (x as isize - k) as usize,
                    });
                    (x, op)
                } else if k == kmax {
                    let (x, mut op) = furthest_xs[offset(n, m, k - 1)].as_ref().unwrap().clone();
                    op.push(EditOp::DeleteLine { orig_line: x });
                    (x + 1, op)
                } else {
                    let &(x1, ref op1) = furthest_xs[offset(n, m, k + 1)].as_ref().unwrap();
                    let &(x2, ref op2) = furthest_xs[offset(n, m, k - 1)].as_ref().unwrap();
                    let x2 = x2 + 1;

                    if x1 > x2 {
                        let mut op = op1.clone();
                        op.push(EditOp::InsertLine {
                            orig_line: x1,
                            mod_line: (x1 as isize - k) as usize,
                        });
                        (x1, op.clone())
                    } else {
                        let mut op = op2.clone();
                        op.push(EditOp::DeleteLine { orig_line: x2 });
                        (x2, op.clone())
                    }
                };
                (x, x as isize - k, op)
            };

            if start_x > n || start_y > m as isize || start_y < 0 {
                continue;
            }

            let start_y = start_y as usize;

            let (mut x, mut y) = (start_x, start_y);

            while x + 1 <= n && y + 1 <= m && src_splits[x + 1] == src_splits[y + 1] {
                x += 1;
                y += 1;
            }

            furthest_xs[offset(n, m, k)] = Some((x, op));

            if x == m && y == m {
                break 'outer;
            }
        }
    }
    let (_, op) = furthest_xs[n + 1].take().unwrap();
    op
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
