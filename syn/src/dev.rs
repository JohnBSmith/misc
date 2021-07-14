

fn debug_print_groups(groups: &SynonymGroups) {
    for t in &groups.list {
        for item in t {
            print!("[");
            io::stdout().write_all(item)?;
            print!("]");
        }
        println!();
    }
}
