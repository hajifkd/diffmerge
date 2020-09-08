use diffmerge::merge;
use std::env;
use std::fs::read;

fn main() -> Result<(), Box<dyn std::error::Error + 'static>> {
    let args: Vec<String> = env::args().collect();
    if args.len() != 4 {
        println!("Usage {} <ANCESTOR> <BRANCH1> <BRANCH2>", &args[0]);
        return Ok(());
    }

    let ancestor = String::from_utf8(read(&args[1])?)?;
    let branch1 = String::from_utf8(read(&args[2])?)?;
    let branch2 = String::from_utf8(read(&args[3])?)?;
    let mut merge = merge(&ancestor, &branch1, &branch2);
    merge.set_names(&args[2], &args[3]);

    println!("{}", merge);

    Ok(())
}
