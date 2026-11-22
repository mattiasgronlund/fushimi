//! Prints the tables of issue #7 from criterion's saved baselines.
//!
//! Usage: `tables <criterion dir> <log> <token log> <issue5.tsv> [--drop <baseline>]...`
//!
//! - `<criterion dir>` is `$CRITERION_HOME`, holding `<benchmark>/<baseline>/` with
//!   baselines `<P0|B|A1>-<L0|L6>-r<k>` and `token-<B|A1>-<L0|L6>-r<k>`.
//! - `<log>` and `<token log>` are criterion's output of one run of each kind
//!   (e.g. `out/B-L0-r1.txt`, `out/token-B-L0-r1.txt`); they give the rows and their order.
//! - `<issue5.tsv>` holds issue #5's `generic 7e92e46 / b5dd856` column: id, ratio, spread.
//! - `--drop` leaves out a whole round dropped for load or sleep.
//!
//! Each cell is the lowest of the kept rounds' medians per element: criterion's
//! `median.point_estimate` in `estimates.json`, divided by the 1024 elements of an
//! iteration. `spread` is the largest difference between the kept rounds of any
//! one build in that row, relative to the lower one.
//!
//! Disturbed rounds, as fixed in the issue before measuring: for each series and
//! round of a build, r = median / min over i of (`times[i]` / `iters[i]`), from
//! `estimates.json` and `sample.json`. A cell drops when its r is more than 0.03
//! above the median r of that build's rounds on that series (with two rounds the
//! median is their mean). A build left with one round is marked `¹`.

use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

const N: f64 = 1024.0;
const R_TOLERANCE: f64 = 0.03;

#[derive(Clone, Copy)]
struct Round {
    /// The median per element, in ns.
    median: f64,
    /// The median over the fastest iteration, both per iteration.
    r: f64,
}

/// Rounds by series, then build (`P0-L0`, `token-B-L6`, ...), then round number.
type Rounds = BTreeMap<String, BTreeMap<String, BTreeMap<u32, Round>>>;

fn read_json(path: &Path) -> Value {
    let text = fs::read_to_string(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

fn find_baselines(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            if path.join("sample.json").is_file() && path.join("benchmark.json").is_file() {
                out.push(path);
            } else {
                find_baselines(&path, out);
            }
        }
    }
}

fn load(root: &Path, drop: &BTreeSet<String>) -> Rounds {
    let mut dirs = Vec::new();
    find_baselines(root, &mut dirs);
    let mut m = Rounds::new();
    for dir in dirs {
        let base = dir.file_name().unwrap().to_str().unwrap().to_owned();
        // criterion's own `base` and `new` are not saved baselines.
        let Some((build, k)) = base.rsplit_once("-r") else {
            continue;
        };
        if drop.contains(&base) {
            continue;
        }
        let bench = read_json(&dir.join("benchmark.json"));
        let id = bench["full_id"].as_str().unwrap().to_owned();
        if bench["throughput"]["Elements"].as_f64() != Some(N) {
            eprintln!("warning: {id} does not time {N} elements per iteration");
        }
        let est = read_json(&dir.join("estimates.json"));
        let median = est["median"]["point_estimate"].as_f64().unwrap();
        let sample = read_json(&dir.join("sample.json"));
        let fastest = sample["times"]
            .as_array()
            .unwrap()
            .iter()
            .zip(sample["iters"].as_array().unwrap())
            .map(|(t, i)| t.as_f64().unwrap() / i.as_f64().unwrap())
            .fold(f64::INFINITY, f64::min);
        let round = Round {
            median: median / N,
            r: median / fastest,
        };
        m.entry(id)
            .or_default()
            .entry(build.to_owned())
            .or_default()
            .insert(k.parse().unwrap(), round);
    }
    m
}

/// The series in criterion's output, in order.
fn rows(log: &Path) -> Vec<String> {
    fs::read_to_string(log)
        .unwrap()
        .lines()
        .filter_map(|l| l.strip_prefix("Benchmarking ")?.strip_suffix(": Analyzing"))
        .map(str::to_owned)
        .collect()
}

fn median(mut xs: Vec<f64>) -> f64 {
    xs.sort_by(f64::total_cmp);
    let n = xs.len();
    if n % 2 == 1 {
        xs[n / 2]
    } else {
        (xs[n / 2 - 1] + xs[n / 2]) / 2.0
    }
}

/// A build's cell in one row, after the rule for disturbed rounds.
#[derive(Clone, Copy)]
struct Cell {
    lo: f64,
    spread: f64,
    /// Only one round is left.
    single: bool,
}

struct Dropped {
    build: String,
    round: u32,
    series: String,
    r: f64,
    median_r: f64,
}

fn cell(m: &Rounds, id: &str, build: &str, dropped: &mut Vec<Dropped>) -> Option<Cell> {
    let rounds = m.get(id)?.get(build)?;
    let median_r = median(rounds.values().map(|x| x.r).collect());
    let mut kept = Vec::new();
    for (&k, x) in rounds {
        if x.r > median_r + R_TOLERANCE {
            dropped.push(Dropped {
                build: build.to_owned(),
                round: k,
                series: id.to_owned(),
                r: x.r,
                median_r,
            });
        } else {
            kept.push(x.median);
        }
    }
    let lo = kept.iter().copied().fold(f64::INFINITY, f64::min);
    let hi = kept.iter().copied().fold(0.0, f64::max);
    Some(Cell {
        lo,
        spread: (hi - lo) / lo,
        single: kept.len() == 1,
    })
}

fn ns(c: Option<Cell>) -> String {
    c.map_or(String::new(), |c| {
        format!("{:.2}{}", c.lo, if c.single { "¹" } else { "" })
    })
}

fn ratio(a: Option<Cell>, b: Option<Cell>) -> Option<f64> {
    Some(a?.lo / b?.lo)
}

fn fmt_ratio(r: Option<f64>) -> String {
    r.map_or(String::new(), |r| format!("{r:.3}×"))
}

fn spread(cells: &[Option<Cell>]) -> f64 {
    cells.iter().flatten().map(|c| c.spread).fold(0.0, f64::max)
}

/// A ratio at one layout: its value, its row's spread, and whether a cell is `¹`.
#[derive(Clone, Copy)]
struct At {
    ratio: f64,
    spread: f64,
    single: bool,
}

impl At {
    /// -1, 0 or 1: whether the ratio differs from 1 by more than the spread.
    fn moves(self) -> i32 {
        if self.ratio > 1.0 + self.spread {
            1
        } else if self.ratio < 1.0 - self.spread {
            -1
        } else {
            0
        }
    }
}

#[derive(Default)]
struct Moves {
    both: Vec<String>,
    one: Vec<String>,
}

fn classify(moves: &mut Moves, id: &str, name: &str, l0: Option<At>, l6: Option<At>) {
    let (Some(a), Some(b)) = (l0, l6) else {
        return;
    };
    if a.single || b.single {
        return;
    }
    let line = format!(
        "{id}, {name}: {:.3}× at L0 (spread {:.1} %), {:.3}× at L6 (spread {:.1} %)",
        a.ratio,
        100.0 * a.spread,
        b.ratio,
        100.0 * b.spread
    );
    match (a.moves(), b.moves()) {
        (0, 0) => {}
        (x, y) if x == y => moves.both.push(line),
        _ => moves.one.push(line),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let root = PathBuf::from(&args[0]);
    let main_rows = rows(Path::new(&args[1]));
    let token_rows = rows(Path::new(&args[2]));
    let issue5: BTreeMap<String, (f64, f64)> = fs::read_to_string(&args[3])
        .unwrap()
        .lines()
        .map(|l| {
            let f: Vec<&str> = l.split('\t').collect();
            (f[0].to_owned(), (f[1].parse().unwrap(), f[2].parse().unwrap()))
        })
        .collect();
    let mut drop = BTreeSet::new();
    let mut i = 4;
    while i < args.len() {
        assert_eq!(args[i], "--drop");
        drop.insert(args[i + 1].clone());
        i += 2;
    }
    let m = load(&root, &drop);
    let mut dropped = Vec::new();
    let mut a1_b = Moves::default();
    let mut b_p0 = Moves::default();
    let mut vs5 = Vec::new();

    let builds: BTreeSet<String> = m
        .values()
        .flat_map(|b| b.iter().flat_map(|(b, r)| r.keys().map(move |k| format!("{b}-r{k}"))))
        .collect();
    println!("Rounds kept: {}", builds.into_iter().collect::<Vec<_>>().join(", "));
    if !drop.is_empty() {
        println!("Rounds dropped: {}", drop.iter().cloned().collect::<Vec<_>>().join(", "));
    }

    // At[layout][0] is B / P0, At[layout][1] is A1 / B.
    let mut at: BTreeMap<&str, [[Option<At>; 2]; 2]> = BTreeMap::new();
    for (li, lay) in ["L0", "L6"].into_iter().enumerate() {
        println!("\n## {lay}\n");
        println!("| Series | P0 (ns) | B (ns) | A1 (ns) | B / P0 | A1 / B | spread |");
        println!("|---|--:|--:|--:|--:|--:|--:|");
        for id in &main_rows {
            let [p0, b, a1] =
                ["P0", "B", "A1"].map(|s| cell(&m, id, &format!("{s}-{lay}"), &mut dropped));
            let s = spread(&[p0, b, a1]);
            let (bp, ab) = (ratio(b, p0), ratio(a1, b));
            println!(
                "| {id} | {} | {} | {} | {} | {} | {:.1} % |",
                ns(p0),
                ns(b),
                ns(a1),
                fmt_ratio(bp),
                fmt_ratio(ab),
                100.0 * s
            );
            let single = |x: &[Option<Cell>]| x.iter().flatten().any(|c| c.single);
            let e = at.entry(id).or_default();
            e[li][0] = bp.map(|ratio| At {
                ratio,
                spread: s,
                single: single(&[b, p0]),
            });
            e[li][1] = ab.map(|ratio| At {
                ratio,
                spread: s,
                single: single(&[a1, b]),
            });
            if lay == "L0" {
                if let (Some(r), Some(&(r5, s5))) = (bp, issue5.get(id.as_str())) {
                    let tol = s.max(s5);
                    if (r / r5 - 1.0).abs() > tol {
                        vs5.push(format!(
                            "{id}: B / P0 {r:.3}× against issue #5's {r5:.3}× (spreads {:.1} % and {:.1} %)",
                            100.0 * s,
                            100.0 * s5
                        ));
                    }
                }
            }
        }
    }
    for id in &main_rows {
        let e = at[id.as_str()];
        classify(&mut b_p0, id, "B / P0", e[0][0], e[1][0]);
        classify(&mut a1_b, id, "A1 / B", e[0][1], e[1][1]);
    }

    println!("\n## token/*\n");
    println!("| Series | B L0 (ns) | A1 L0 (ns) | A1 / B L0 | spread L0 | B L6 (ns) | A1 L6 (ns) | A1 / B L6 | spread L6 |");
    println!("|---|--:|--:|--:|--:|--:|--:|--:|--:|");
    for id in &token_rows {
        print!("| {id} |");
        let mut ats = [None; 2];
        for (li, lay) in ["L0", "L6"].into_iter().enumerate() {
            let [b, a1] = ["B", "A1"].map(|s| cell(&m, id, &format!("token-{s}-{lay}"), &mut dropped));
            let s = spread(&[b, a1]);
            let r = ratio(a1, b);
            print!(" {} | {} | {} | {:.1} % |", ns(b), ns(a1), fmt_ratio(r), 100.0 * s);
            ats[li] = r.map(|ratio| At {
                ratio,
                spread: s,
                single: [b, a1].iter().flatten().any(|c| c.single),
            });
        }
        println!();
        classify(&mut a1_b, id, "A1 / B", ats[0], ats[1]);
    }

    println!("\n## Cells dropped by the rule for disturbed rounds\n");
    if dropped.is_empty() {
        println!("None.");
    } else {
        println!("| Build | Round | Series | r | median r |");
        println!("|---|--:|---|--:|--:|");
        for d in &dropped {
            println!(
                "| {} | {} | {} | {:.4} | {:.4} |",
                d.build, d.round, d.series, d.r, d.median_r
            );
        }
    }
    for (name, mv) in [("A1 / B", &a1_b), ("B / P0", &b_p0)] {
        println!("\n## Moves of {name}\n");
        println!("At both layouts, in the same direction ({}):", mv.both.len());
        for l in &mv.both {
            println!("- {l}");
        }
        println!("\nAt one layout only, or in opposite directions ({}):", mv.one.len());
        for l in &mv.one {
            println!("- {l}");
        }
    }
    println!("\n## B / P0 at L0 against issue #5's generic 7e92e46 / b5dd856\n");
    println!("Rows that differ by more than the larger spread ({}):", vs5.len());
    for l in &vs5 {
        println!("- {l}");
    }
}
