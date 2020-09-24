use std::fmt::Display;
use std::path::Path;

mod bitvec;
mod candidate_path;
mod cfg;
mod cli;
mod compile;
mod dead_code_elimination;
mod decode;
mod disassemble;
mod elf;
mod formula_graph;
mod iterator;
mod smt;
mod solver;
mod ternary;

use compile::compile_example;
use disassemble::disassemble_riscu;

fn main() {
    let matches = cli::args().get_matches();

    fn handle_error<R, E, F>(f: F) -> R
    where
        E: Display,
        F: FnOnce() -> Result<R, E>,
    {
        match f() {
            Err(e) => {
                eprintln!("{}", e);
                std::process::exit(1);
            }
            Ok(x) => x,
        }
    }

    match matches.subcommand() {
        Some(("disassemble", disassemble_args)) => handle_error(|| {
            let input = Path::new(disassemble_args.value_of("input-file").unwrap());
            disassemble_riscu(Path::new(input))
        }),
        Some(("compile", compiler_args)) => handle_error(|| -> Result<(), String> {
            let compiler = compiler_args.value_of("compiler").unwrap();

            let input = Path::new(compiler_args.value_of("input-file").unwrap());

            compile_example(input, Some(compiler))?;

            Ok(())
        }),
        Some(("cfg", cfg_args)) => {
            handle_error(|| -> Result<(), String> {
                let input = Path::new(cfg_args.value_of("input-file").unwrap());
                let output = Path::new(cfg_args.value_of("output-file").unwrap());

                let (graph, _, _) = cfg::build_from_file(Path::new(input))?;

                if let Some(_format @ "png") = cfg_args.value_of("format") {
                    let tmp = Path::new(".tmp-cfg.dot");

                    cfg::write_to_file(&graph, tmp).map_err(|e| e.to_string())?;

                    cfg::convert_dot_to_png(tmp, output)?;

                    std::fs::remove_file(tmp).map_err(|e| e.to_string())?;
                } else {
                    cfg::write_to_file(&graph, output).map_err(|e| e.to_string())?;
                }

                Ok(())
            });
        }
        Some(("smt", _cfg_args)) => {
            handle_error(|| -> Result<(), String> {
                use crate::candidate_path::create_candidate_paths;
                use crate::formula_graph::build_dataflow_graph;
                use petgraph::dot::Dot;
                use std::env::current_dir;
                use std::fs::File;
                use std::io::Write;
                use std::process::Command;

                let cd = String::from(current_dir().unwrap().to_str().unwrap());

                // generate RISC-U binary with Selfie
                let _ = Command::new("docker")
                    .arg("run")
                    .arg("-v")
                    .arg(cd + ":/opt/monster")
                    .arg("cksystemsteaching/selfie")
                    .arg("/opt/selfie/selfie")
                    .arg("-c")
                    .arg("/opt/monster/symbolic/symbolic-exit.c")
                    .arg("-o")
                    .arg("/opt/monster/symbolic/symbolic-exit.riscu.o")
                    .output();

                let test_file = Path::new("symbolic/symbolic-exit.riscu.o");

                let (graph, data_segment, elf_metadata) = cfg::build_from_file(test_file).unwrap();

                // println!("{:?}", data_segment);

                let (path, branch_decisions) = create_candidate_paths(&graph)[0].clone();

                // println!("{:?}", path);

                let (formula, _root) = build_dataflow_graph(
                    &path,
                    data_segment.as_slice(),
                    &elf_metadata,
                    branch_decisions,
                )
                .unwrap();

                let dot_graph = Dot::with_config(&formula, &[]);

                let mut f = File::create("tmp-graph.dot").unwrap();
                f.write_fmt(format_args!("{:?}", dot_graph)).unwrap();

                smt::smt(&formula);

                Ok(())
            });
        }
        _ => unreachable!(),
    }
}
