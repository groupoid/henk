fn main() {
    lalrpop::process_root().unwrap();
    println!("cargo:rerun-if-changed=src/parser.lalrpop")
}
