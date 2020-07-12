use diffmerge::diff;

fn main() {
    dbg!(diff(
        &"a
b
c
d
e
f
g"
        .split('\n')
        .collect::<Vec<_>>(),
        &"a
c
b
c
d
f
g
h
i
j"
        .split('\n')
        .collect::<Vec<_>>()
    ));
}
