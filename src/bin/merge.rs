use diffmerge::merge;

fn main() {
        println!(
                "{}",
                merge(
                        "a
b
c
d
e
k
f",
                        "a
c
d
e1
k
fz",
                        "a
c
d
e2
k
fz
"
                )
        );
}
