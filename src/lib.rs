use std::collections::HashMap;

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum EditOp {
    DeleteLine { orig_line: usize },
    InsertLine { orig_line: usize, mod_line: usize },
}

impl EditOp {
    fn orig_line(&self) -> usize {
        match self {
            &EditOp::DeleteLine { orig_line } => orig_line,
            &EditOp::InsertLine { orig_line, .. } => orig_line,
        }
    }

    fn equal_as_op(&self, another: &Self, self_lines: &[&str], another_lines: &[&str]) -> bool {
        match self {
            &EditOp::DeleteLine { .. } => self == another,
            &EditOp::InsertLine {
                orig_line: self_orig_line,
                mod_line: self_mod_line,
            } => match another {
                &EditOp::InsertLine {
                    orig_line: another_orig_line,
                    mod_line: another_mod_line,
                } => {
                    dbg!((self_mod_line, another_mod_line));
                    self_orig_line == another_orig_line
                        && self_lines[self_mod_line] == another_lines[another_mod_line]
                }
                _ => false,
            },
        }
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum MergedLine<'a> {
    Line(&'a str),
    Conflict {
        candidate1: Vec<&'a str>,
        candidate2: Vec<&'a str>,
    },
}

// レーベンシュタイン距離を深さ優先でグリーディに求める
// O((n + m) * d) see https://link.springer.com/article/10.1007/BF01840446
pub fn diff(src_lines: &[&str], dst_lines: &[&str]) -> Vec<EditOp> {
    let n = src_lines.len();
    let m = dst_lines.len();
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

            while x + 1 <= n && y + 1 <= m && src_lines[x] == dst_lines[y] {
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
                orig_line: x,
                mod_line: (x as isize - k) as usize - 1,
            })
        } else {
            result.push(EditOp::DeleteLine { orig_line: x - 1 })
        }
    }

    result
}

fn collect_lines<'a>(
    lines: &[&'a str],
    diff: &[EditOp],
    n: usize,
    i: usize,
    j: &mut usize,
) -> Vec<&'a str> {
    let mut result = vec![];
    while *j < n && diff[n - *j - 1].orig_line() == i {
        match diff[n - *j - 1] {
            EditOp::InsertLine { mod_line, .. } => result.push(lines[mod_line]),
            _ => (),
        }
        *j += 1;
    }
    result
}

pub fn merge<'a>(ancestor: &'a str, desc1: &'a str, desc2: &'a str) -> Vec<MergedLine<'a>> {
    let ans_lines: Vec<&str> = ancestor.split('\n').collect();
    let d1_lines: Vec<&str> = desc1.split('\n').collect();
    let d2_lines: Vec<&str> = desc2.split('\n').collect();
    let diff1 = diff(&ans_lines, &d1_lines);
    let diff2 = diff(&ans_lines, &d2_lines);
    let mut j_d1 = 0;
    let mut j_d2 = 0;
    let n_d1 = diff1.len();
    let n_d2 = diff2.len();

    let mut result = vec![];

    for i in 0..ans_lines.len() {
        if j_d1 >= n_d1
            || j_d2 >= n_d2
            || diff1[n_d1 - j_d1 - 1].orig_line() != i
            || diff2[n_d2 - j_d2 - 1].orig_line() != i
        {
            result.push(MergedLine::Line(ans_lines[i]));
            continue;
        }
        while j_d1 < n_d1
            && j_d2 < n_d2
            && diff1[n_d1 - j_d1 - 1].orig_line() == i
            && diff2[n_d2 - j_d2 - 1].orig_line() == i
        {
            if diff1[n_d1 - j_d1 - 1].equal_as_op(&diff2[n_d2 - j_d2 - 1], &d1_lines, &d2_lines) {
                match diff1[n_d1 - j_d1 - 1] {
                    EditOp::InsertLine { mod_line, .. } => {
                        result.push(MergedLine::Line(d1_lines[mod_line]));
                    }
                    _ => (),
                }
                j_d1 += 1;
                j_d2 += 1;
            } else {
                let candidate1 = collect_lines(&d1_lines, &diff1, n_d1, i, &mut j_d1);
                let candidate2 = collect_lines(&d2_lines, &diff2, n_d2, i, &mut j_d2);
                result.push(MergedLine::Conflict {
                    candidate1,
                    candidate2,
                });
            }
        }

        while j_d1 < n_d1 && diff1[n_d1 - j_d1 - 1].orig_line() == i {
            match diff1[n_d1 - j_d1 - 1] {
                EditOp::InsertLine { mod_line, .. } => {
                    result.push(MergedLine::Line(d1_lines[mod_line]));
                }
                _ => (),
            }
            j_d1 += 1;
        }

        while j_d2 < n_d2 && diff2[n_d2 - j_d2 - 1].orig_line() == i {
            match diff2[n_d2 - j_d2 - 1] {
                EditOp::InsertLine { mod_line, .. } => {
                    result.push(MergedLine::Line(d2_lines[mod_line]));
                }
                _ => (),
            }
            j_d2 += 1;
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
            .map(|_| alphabets[random::<usize>() % alphabets.len()])
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
            let mut src_lines: Vec<_> = src.split('\n').collect();
            let dst_lines: Vec<_> = dst.split('\n').collect();
            let ops = diff(&src_lines, &dst_lines);

            for op in ops {
                match op {
                    EditOp::DeleteLine { orig_line } => {
                        src_lines.remove(orig_line);
                    }
                    EditOp::InsertLine {
                        orig_line,
                        mod_line,
                    } => {
                        src_lines.insert(orig_line, dst_lines[mod_line]);
                    }
                }
            }

            assert_eq!(src_lines, dst_lines);
        }
    }
}
