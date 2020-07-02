use diffmerge::diff;

fn main() {
    dbg!(diff(
        "a
b
c
d
e
f
g",
        "a
c
b
c
d
f
"
    ));
}
