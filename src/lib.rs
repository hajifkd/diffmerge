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

impl<'a> MergedLine<'a> {
    pub fn is_conflicted(&self) -> bool {
        match self {
            &MergedLine::Conflict { .. } => true,
            _ => false,
        }
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct Merge<'a> {
    lines: Vec<MergedLine<'a>>,
    merge_names: Option<(&'a str, &'a str)>,
}

impl<'a> Merge<'a> {
    pub fn new(lines: Vec<MergedLine<'a>>) -> Self {
        Merge {
            lines,
            merge_names: None,
        }
    }
    pub fn is_successful(&self) -> bool {
        self.lines.iter().all(|m| !m.is_conflicted())
    }

    pub fn set_names(&mut self, name1: &'a str, name2: &'a str) {
        self.merge_names = Some((name1, name2));
    }
}

impl<'a> std::fmt::Display for Merge<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, line) in self.lines.iter().enumerate() {
            if i != 0 {
                write!(f, "\n")?;
            }
            match line {
                &MergedLine::Line(l) => {
                    write!(f, "{}", l)?;
                }
                &MergedLine::Conflict {
                    ref candidate1,
                    ref candidate2,
                } => {
                    let (name1, name2) = self.merge_names.unwrap_or(("", ""));
                    write!(f, "<<<<<<< {}\n", name1)?;
                    for l1 in candidate1.iter() {
                        write!(f, "{}\n", l1)?;
                    }
                    write!(f, "=======\n")?;
                    for l2 in candidate2.iter() {
                        write!(f, "{}\n", l2)?;
                    }
                    write!(f, ">>>>>>> {}", name2)?;
                }
            }
        }

        Ok(())
    }
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
) -> (bool, Vec<&'a str>) {
    let mut result = vec![];
    let mut delete_line = false;
    while *j < n && diff[n - *j - 1].orig_line() == i {
        match diff[n - *j - 1] {
            EditOp::InsertLine { mod_line, .. } => result.push(lines[mod_line]),
            EditOp::DeleteLine { .. } => {
                delete_line = true;
            }
        }
        *j += 1;
    }
    (delete_line, result)
}

pub fn merge<'a>(ancestor: &'a str, desc1: &'a str, desc2: &'a str) -> Merge<'a> {
    let ans_lines: Vec<&str> = ancestor.split('\n').collect();
    let d1_lines: Vec<&str> = desc1.split('\n').collect();
    let d2_lines: Vec<&str> = desc2.split('\n').collect();
    let diff1 = diff(&ans_lines, &d1_lines);
    let diff2 = diff(&ans_lines, &d2_lines);
    let mut j_d1 = 0;
    let mut j_d2 = 0;
    let n_d1 = diff1.len();
    let n_d2 = diff2.len();
    dbg!(&diff1);
    dbg!(&diff2);

    let mut result = vec![];

    'ans_loop: for i in 0..=ans_lines.len() {
        while j_d1 < n_d1
            && j_d2 < n_d2
            && diff1[n_d1 - j_d1 - 1].orig_line() == i
            && diff2[n_d2 - j_d2 - 1].orig_line() == i
        {
            if diff1[n_d1 - j_d1 - 1].equal_as_op(&diff2[n_d2 - j_d2 - 1], &d1_lines, &d2_lines) {
                j_d1 += 1;
                j_d2 += 1;
                match diff1[n_d1 - j_d1] {
                    EditOp::InsertLine { mod_line, .. } => {
                        result.push(MergedLine::Line(d1_lines[mod_line]));
                    }
                    EditOp::DeleteLine { .. } => {
                        continue 'ans_loop;
                    }
                }
            } else {
                let (d1, mut candidate1) = collect_lines(&d1_lines, &diff1, n_d1, i, &mut j_d1);
                let (d2, mut candidate2) = collect_lines(&d2_lines, &diff2, n_d2, i, &mut j_d2);

                if d1 != d2 {
                    if d1 {
                        candidate2.push(ans_lines[i]);
                    } else {
                        candidate1.push(ans_lines[i]);
                    }
                }

                result.push(MergedLine::Conflict {
                    candidate1,
                    candidate2,
                });

                if d1 || d2 {
                    continue 'ans_loop;
                }
            }
        }

        while j_d1 < n_d1 && diff1[n_d1 - j_d1 - 1].orig_line() == i {
            j_d1 += 1;
            match diff1[n_d1 - j_d1] {
                EditOp::InsertLine { mod_line, .. } => {
                    result.push(MergedLine::Line(d1_lines[mod_line]));
                }
                EditOp::DeleteLine { .. } => {
                    continue 'ans_loop;
                }
            }
        }

        while j_d2 < n_d2 && diff2[n_d2 - j_d2 - 1].orig_line() == i {
            j_d2 += 1;
            match diff2[n_d2 - j_d2] {
                EditOp::InsertLine { mod_line, .. } => {
                    result.push(MergedLine::Line(d2_lines[mod_line]));
                }
                EditOp::DeleteLine { .. } => {
                    continue 'ans_loop;
                }
            }
        }

        if i < ans_lines.len()
            && (j_d1 >= n_d1 || diff1[n_d1 - j_d1 - 1].orig_line() != i)
            && (j_d2 >= n_d2 || diff2[n_d2 - j_d2 - 1].orig_line() != i)
        {
            result.push(MergedLine::Line(ans_lines[i]));
        }
    }

    dbg!(&result);
    Merge::new(result)
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

    #[test]
    fn test_merge() {
        let merged = merge(
            "1\n2\n3\n4\n5\n6\n7\n8\n",
            "1\n2\n2\n2\n3\n5\n6\n7\n8\n",
            "1\n2\n3\n4\n5\n6\n6\n6\n6\n8\n",
        );
        assert_eq!(merged.is_successful(), true);
        assert_eq!(format!("{}", merged), "1\n2\n2\n2\n3\n5\n6\n6\n6\n6\n8\n");

        let merged = merge(
            "a\nb\nc\nd\ne\nf\ng\nh",
            "a\nc\nd\ne\nz\ng\nh",
            "a\nb\nc\ny\ne\nz\ng\nh\ni\nj\nk",
        );
        assert_eq!(merged.is_successful(), true);
        assert_eq!(format!("{}", merged), "a\nc\ny\ne\nz\ng\nh\ni\nj\nk");

        let mut merged = merge(
            "a\nb\nc\nd\ne\nf\ng\nh",
            "a\nz\nc\nw\ny\nq\ng\nh\ni\nj\nk\nl\nn\nm",
            "a\nx\nc\nw\ny\nq\ng\nh\ni\nj\nc\nl\nn\nm",
        );
        assert_eq!(merged.is_successful(), false);
        assert_eq!(
            format!("{}", merged),
            "a\n<<<<<<< \nz\n=======\nx\n>>>>>>> \nc\nw\ny\nq\ng\nh\ni\nj\n<<<<<<< \nk\nl\nn\nm\n=======\nc\nl\nn\nm\n>>>>>>> "
        );
        merged.set_names("branch1", "branch2");
        assert_eq!(
            format!("{}", merged),
            "a\n<<<<<<< branch1\nz\n=======\nx\n>>>>>>> branch2\nc\nw\ny\nq\ng\nh\ni\nj\n<<<<<<< branch1\nk\nl\nn\nm\n=======\nc\nl\nn\nm\n>>>>>>> branch2"
        );
    }
}
