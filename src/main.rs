use env_logger::{Env, TimestampPrecision};
use log::error;
use std::{fmt::Display, path::Path};

mod cli;

use monster::{
    cfg::{build_cfg_from_file, write_to_file},
    disassemble::disassemble_riscu,
    engine,
    exploration_strategy::ShortestPathStrategy,
};

fn handle_error<R, E, F>(f: F) -> R
where
    E: Display,
    F: FnOnce() -> Result<R, E>,
{
    match f() {
        Err(e) => {
            error!("{}", e);
            std::process::exit(1);
        }
        Ok(x) => x,
    }
}

fn main() {
    let matches = cli::args().get_matches();

    let log_level = matches
        .value_of("verbose")
        .expect("log level has to be set in CLI at all times");

    let env = Env::new()
        .filter_or("MONSTER_LOG", log_level)
        .write_style_or("MONSTER_LOG_STYLE", "always");

    env_logger::Builder::from_env(env)
        .format_timestamp(Some(TimestampPrecision::Millis))
        .init();

    match matches.subcommand() {
        Some(("disassemble", disassemble_args)) => handle_error(|| {
            let input = Path::new(disassemble_args.value_of("input-file").unwrap());
            disassemble_riscu(Path::new(input))
        }),
        Some(("cfg", cfg_args)) => {
            handle_error(|| -> Result<(), String> {
                let input = Path::new(cfg_args.value_of("input-file").unwrap());
                let output = Path::new(cfg_args.value_of("output-file").unwrap());
                let distances = cfg_args.is_present("distances");

                let ((cfg, _), program) = build_cfg_from_file(Path::new(input))?;

                if distances {
                    ShortestPathStrategy::new(&cfg, program.entry_address)
                        .write_cfg_with_distances_to_file(output)
                        .map_err(|e| e.to_string())?;
                } else {
                    write_to_file(&cfg, output).map_err(|e| e.to_string())?;
                }

                Ok(())
            });
        }
        Some(("execute", args)) => {
            handle_error(|| -> Result<(), String> {
                let input = Path::new(args.value_of("input-file").unwrap());
                let solver = args.value_of("solver").unwrap();

                engine::execute(
                    input,
                    match solver {
                        "monster" => engine::Backend::Monster,
                        "boolector" => engine::Backend::Boolector,
                        "z3" => engine::Backend::Z3,
                        _ => unreachable!(),
                    },
                )
            });
        }
        _ => unreachable!(),
    }
}
