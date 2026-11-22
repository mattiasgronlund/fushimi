//! Prints the tables of issue #6 from criterion's saved baselines.
//!
//! Usage: `tables <criterion dir> <log> [--drop <baseline>]... [--prev <dir> <rounds>]`
//!
//! - `<criterion dir>` is `$CRITERION_HOME`, holding `<benchmark>/<config>-r<k>/`.
//! - `<log>` is criterion's output of a run of `primitives` and `intervals`
//!   (e.g. `out/neon-r1.txt`); it gives each benchmark's bench file and the
//!   order of the rows.
//! - `--drop` leaves a round out, e.g. `--drop generic-r1`.
//! - `--prev` compares with issue #4's baselines in `<dir>`, keeping only the
//!   rounds listed in `<rounds>` (comma-separated, as on the first line of its
//!   `tables.md`).
//!
//! Each cell is the lowest of the kept rounds' medians per element: criterion's
//! `median.point_estimate` in `estimates.json`, divided by the 1024 elements of
//! an iteration. `spread` is the largest difference between the rounds of any one
//! configuration in that row, relative to the lower one.

use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

const N: f64 = 1024.0;

/// Medians per element, by benchmark id, then configuration, then round.
type Medians = BTreeMap<String, BTreeMap<String, BTreeMap<String, f64>>>;

fn read_json(path: &Path) -> Value {
    let text = fs::read_to_string(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

fn find_baselines(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            if path.join("estimates.json").is_file() && path.join("benchmark.json").is_file() {
                out.push(path);
            } else {
                find_baselines(&path, out);
            }
        }
    }
}

/// Reads every baseline `<config>-r<k>` under `root` whose name `keep` accepts.
fn load(root: &Path, keep: impl Fn(&str) -> bool) -> Medians {
    let mut dirs = Vec::new();
    find_baselines(root, &mut dirs);
    let mut m = Medians::new();
    for dir in dirs {
        let base = dir.file_name().unwrap().to_str().unwrap().to_owned();
        // criterion's own `base` and `new` are not saved baselines.
        let Some((config, round)) = base.rsplit_once("-r") else {
            continue;
        };
        if !keep(&base) {
            continue;
        }
        let bench = read_json(&dir.join("benchmark.json"));
        let id = bench["full_id"].as_str().unwrap().to_owned();
        assert_eq!(bench["throughput"]["Elements"].as_f64(), Some(N), "{id}");
        let est = read_json(&dir.join("estimates.json"));
        let median = est["median"]["point_estimate"].as_f64().unwrap() / N;
        m.entry(id)
            .or_default()
            .entry(config.to_owned())
            .or_default()
            .insert(round.to_owned(), median);
    }
    m
}

/// The bench file and id of every benchmark in criterion's output, in order.
fn rows(log: &Path) -> Vec<(String, String)> {
    let text = fs::read_to_string(log).unwrap();
    let mut file = String::new();
    let mut out = Vec::new();
    for line in text.lines() {
        if let Some(rest) = line.trim().strip_prefix("Running benches/") {
            file = rest.split(".rs").next().unwrap().to_owned();
        } else if let Some(id) = line
            .strip_prefix("Benchmarking ")
            .and_then(|l| l.strip_suffix(": Analyzing"))
        {
            out.push((file.clone(), id.to_owned()));
        }
    }
    out
}

/// The lowest median of `config` in row `id`, and its rounds' spread.
fn cell(m: &Medians, id: &str, config: &str) -> Option<(f64, f64)> {
    let rounds = m.get(id)?.get(config)?;
    let lo = rounds.values().copied().fold(f64::INFINITY, f64::min);
    let hi = rounds.values().copied().fold(0.0, f64::max);
    (!rounds.is_empty()).then(|| (lo, (hi - lo) / lo))
}

fn ns(c: Option<(f64, f64)>) -> String {
    c.map_or(String::new(), |(lo, _)| format!("{lo:.2}"))
}

fn ratio(a: Option<(f64, f64)>, b: Option<(f64, f64)>) -> String {
    match (a, b) {
        (Some((a, _)), Some((b, _))) => format!("{:.2}×", a / b),
        _ => String::new(),
    }
}

fn spread(cells: &[Option<(f64, f64)>]) -> f64 {
    cells.iter().flatten().map(|c| c.1).fold(0.0, f64::max)
}

fn main_table(m: &Medians, ids: &[&str]) {
    println!("| Benchmark | fpcr (ns) | generic (ns) | neon (ns) | neon / fpcr | neon / generic | spread |");
    println!("|---|--:|--:|--:|--:|--:|--:|");
    for id in ids {
        let [f, g, n] = ["fpcr", "generic", "neon"].map(|c| cell(m, id, c));
        println!(
            "| {id} | {} | {} | {} | {} | {} | {:.0}% |",
            ns(f),
            ns(g),
            ns(n),
            ratio(n, f),
            ratio(n, g),
            100.0 * spread(&[f, g, n])
        );
    }
}

fn variants_table(m: &Medians, ids: &[&str]) {
    const V: [&str; 4] = ["V1", "V24", "V6s", "V246s"];
    print!("| Benchmark | neon (ns) |");
    for v in V {
        print!(" {v} (ns) |");
    }
    for v in V {
        print!(" {v} / neon |");
    }
    println!(" generic (ns) | spread |");
    println!("|---|--:|{}--:|--:|", "--:|".repeat(2 * V.len()));
    for id in ids {
        let n = cell(m, id, "neon");
        let vs = V.map(|v| cell(m, id, v));
        let g = cell(m, id, "generic");
        print!("| {id} | {} |", ns(n));
        for v in vs {
            print!(" {} |", ns(v));
        }
        for v in vs {
            print!(" {} |", ratio(v, n));
        }
        let mut all = vs.to_vec();
        all.extend([n, g]);
        println!(" {} | {:.0}% |", ns(g), 100.0 * spread(&all));
    }
}

/// Compares this session's `fpcr`, `generic` and `neon` with issue #4's
/// `aarch64`, `generic` and `proto`. Two cells agree when their ratio differs
/// from 1 by at most the larger of the two configurations' spreads in that row.
fn compare(m: &Medians, prev: &Medians, ids: &[&str]) {
    let pairs = [("fpcr", "aarch64"), ("generic", "generic"), ("neon", "proto")];
    let mut common = 0;
    let mut differ = Vec::new();
    for id in ids {
        if !prev.contains_key(*id) {
            continue;
        }
        common += 1;
        for (now, then) in pairs {
            let (Some(a), Some(b)) = (cell(m, id, now), cell(prev, id, then)) else {
                continue;
            };
            let tol = a.1.max(b.1);
            if (a.0 / b.0 - 1.0).abs() > tol {
                differ.push(format!(
                    "| {id} | {now} / #4 {then} | {:.2} | {:.2} | {:.2}× | {:.0}% |",
                    a.0,
                    b.0,
                    a.0 / b.0,
                    100.0 * tol
                ));
            }
        }
    }
    println!("Benchmarks in both issues: {common}; cells that don't agree: {}", differ.len());
    println!();
    println!("| Benchmark | Columns | this (ns) | #4 (ns) | ratio | larger spread |");
    println!("|---|---|--:|--:|--:|--:|");
    for line in differ {
        println!("{line}");
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let root = PathBuf::from(&args[0]);
    let log = PathBuf::from(&args[1]);
    let mut drop = BTreeSet::new();
    let mut prev = None;
    let mut i = 2;
    while i < args.len() {
        match args[i].as_str() {
            "--drop" => {
                drop.insert(args[i + 1].clone());
                i += 2;
            }
            "--prev" => {
                let keep: BTreeSet<String> = args[i + 2].split(',').map(str::to_owned).collect();
                prev = Some(load(Path::new(&args[i + 1]), |b| keep.contains(b)));
                i += 3;
            }
            a => panic!("unknown argument {a}"),
        }
    }
    let m = load(&root, |b| !drop.contains(b));
    let rows = rows(&log);
    let of = |file: &str| -> Vec<&str> {
        rows.iter()
            .filter(|(f, _)| f == file)
            .map(|(_, id)| id.as_str())
            .collect()
    };
    let rounds: BTreeSet<String> = m
        .values()
        .flat_map(|c| c.iter().flat_map(|(c, r)| r.keys().map(move |k| format!("{c}-r{k}"))))
        .collect();
    println!("Rounds kept: {}", rounds.into_iter().collect::<Vec<_>>().join(", "));
    if !drop.is_empty() {
        println!("Rounds dropped: {}", drop.iter().cloned().collect::<Vec<_>>().join(", "));
    }
    println!("\n## Interval operations (`intervals`)\n");
    main_table(&m, &of("intervals"));
    println!("\n## Primitives (`primitives`)\n");
    main_table(&m, &of("primitives"));
    println!("\n## Variants of `mul_add_ru`\n");
    let filtered: Vec<&str> = rows
        .iter()
        .map(|(_, id)| id.as_str())
        .filter(|id| id.starts_with("mul_add") || id.contains("horner8_mul_add"))
        .collect();
    variants_table(&m, &filtered);
    if let Some(prev) = prev {
        println!("\n## Against issue #4\n");
        let all: Vec<&str> = rows.iter().map(|(_, id)| id.as_str()).collect();
        compare(&m, &prev, &all);
    }
}
