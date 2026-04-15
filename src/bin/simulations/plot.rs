// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Plotting module for generating simulation result visualizations.
//!
//! Replaces the Python plotting scripts (latency_histogram.py, bandwidth_plot.py,
//! num_shreds.py) by reading CSV data and producing PNG plots using the
//! `plotters` crate.

use std::path::{Path, PathBuf};

use color_eyre::Result;
use plotters::prelude::*;

const PLOT_WIDTH: u32 = 1200;
const PLOT_HEIGHT: u32 = 700;

fn chart_color(idx: usize) -> RGBColor {
    match idx {
        0 => BLUE,
        1 => RED,
        2 => GREEN,
        3 => MAGENTA,
        4 => CYAN,
        5 => BLACK,
        6 => YELLOW,
        _ => RGBColor(255, 165, 0),
    }
}

const ORANGE: RGBColor = RGBColor(255, 165, 0);

fn output_dir(subdir: &str) -> PathBuf {
    PathBuf::from("data")
        .join("output")
        .join("simulations")
        .join(subdir)
}

fn ensure_dir(path: &Path) -> Result<()> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    Ok(())
}

struct CsvData {
    headers: Vec<String>,
    rows: Vec<Vec<String>>,
}

impl CsvData {
    fn from_file(path: impl AsRef<Path>) -> Result<Self> {
        let mut reader = csv::Reader::from_path(path.as_ref())?;
        let headers = reader.headers()?.iter().map(String::from).collect();
        let mut rows = Vec::new();
        for record in reader.records() {
            let record = record?;
            rows.push(record.iter().map(String::from).collect());
        }
        Ok(Self { headers, rows })
    }

    fn column_index(&self, name: &str) -> Option<usize> {
        self.headers.iter().position(|h| h.trim() == name)
    }

    fn column_f64(&self, name: &str) -> Result<Vec<f64>> {
        let idx = self.column_index(name).ok_or_else(|| {
            std::io::Error::new(
                std::io::ErrorKind::NotFound,
                format!("column '{}' not found in CSV", name),
            )
        })?;
        self.rows
            .iter()
            .map(|row| {
                row[idx].trim().parse::<f64>().map_err(|e| {
                    std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        format!("failed to parse '{}': {}", row[idx], e),
                    )
                })
            })
            .collect::<Result<Vec<f64>, _>>()
            .map_err(|e| color_eyre::eyre::eyre!("{e}"))
    }

    fn column_f64_or(&self, name: &str, default: f64) -> Vec<f64> {
        match self.column_f64(name) {
            Ok(v) => v,
            Err(_) => vec![default; self.rows.len()],
        }
    }
}

#[allow(dead_code)]
struct BarSeries {
    label: &'static str,
    values: Vec<f64>,
    color: RGBColor,
}

macro_rules! draw_stacked_bars {
    ($chart:expr, $x_values:expr, $series:expr, $bar_width:expr, $baseline_init:expr) => {{
        let n = $x_values.len();
        let mut baselines = vec![$baseline_init; n];
        for s in $series {
            let bases = baselines.clone();
            $chart.draw_series($x_values.iter().zip(s.values.iter()).zip(bases.iter()).map(
                |((&x, &v), &b)| {
                    Rectangle::new(
                        [(x - $bar_width / 2.0, b), (x + $bar_width / 2.0, b + v)],
                        s.color.filled(),
                    )
                },
            ))?;
            for (i, &v) in s.values.iter().enumerate() {
                baselines[i] += v;
            }
        }
    }};
}

fn plot_stacked_bar_linear(
    output_path: &Path,
    title: &str,
    x_label: &str,
    y_label: &str,
    x_values: &[f64],
    series: &[BarSeries],
    y_min: f64,
    y_max: f64,
) -> Result<()> {
    ensure_dir(output_path)?;
    let root = BitMapBackend::new(output_path, (PLOT_WIDTH, PLOT_HEIGHT)).into_drawing_area();
    root.fill(&WHITE)?;
    let x_max = x_values.last().copied().unwrap_or(100.0) + 1.0;
    let x_min_val = x_values.first().copied().unwrap_or(0.0) - 1.0;
    let mut chart = ChartBuilder::on(&root)
        .caption(title, ("sans-serif", 20))
        .set_label_area_size(LabelAreaPosition::Left, 80)
        .set_label_area_size(LabelAreaPosition::Bottom, 50)
        .build_cartesian_2d(x_min_val..x_max, y_min..y_max)?;
    chart
        .configure_mesh()
        .x_desc(x_label)
        .y_desc(y_label)
        .draw()?;
    let bar_width = if x_values.len() > 1 {
        (x_values[1] - x_values[0]) * 0.9
    } else {
        1.0
    };
    draw_stacked_bars!(chart, x_values, series, bar_width, 0.0f64);
    root.present()?;
    Ok(())
}

fn plot_stacked_bar_log_y(
    output_path: &Path,
    title: &str,
    x_label: &str,
    y_label: &str,
    x_values: &[f64],
    series: &[BarSeries],
    y_min: f64,
    y_max: f64,
) -> Result<()> {
    ensure_dir(output_path)?;
    let root = BitMapBackend::new(output_path, (PLOT_WIDTH, PLOT_HEIGHT)).into_drawing_area();
    root.fill(&WHITE)?;
    let x_max = x_values.last().copied().unwrap_or(1300.0) + 10.0;
    let x_min_val = x_values.first().copied().unwrap_or(0.0) - 10.0;
    let mut chart = ChartBuilder::on(&root)
        .caption(title, ("sans-serif", 20))
        .set_label_area_size(LabelAreaPosition::Left, 80)
        .set_label_area_size(LabelAreaPosition::Bottom, 50)
        .build_cartesian_2d(x_min_val..x_max, (y_min..y_max).log_scale())?;
    chart
        .configure_mesh()
        .x_desc(x_label)
        .y_desc(y_label)
        .draw()?;
    let bar_width = if x_values.len() > 1 {
        (x_values[1] - x_values[0]) * 0.9
    } else {
        1.0
    };
    draw_stacked_bars!(chart, x_values, series, bar_width, 0.01f64);
    root.present()?;
    Ok(())
}

fn plot_grouped_bar_log(
    output_path: &Path,
    title: &str,
    x_label: &str,
    y_label: &str,
    x_labels: &[String],
    groups: &[BarSeries],
    y_min: f64,
    y_max: f64,
) -> Result<()> {
    ensure_dir(output_path)?;
    let root = BitMapBackend::new(output_path, (PLOT_WIDTH, PLOT_HEIGHT)).into_drawing_area();
    root.fill(&WHITE)?;
    let num_groups = x_labels.len();
    let num_series = groups.len();
    let bar_width = 0.8 / num_series as f64;
    let mut chart = ChartBuilder::on(&root)
        .caption(title, ("sans-serif", 20))
        .set_label_area_size(LabelAreaPosition::Left, 80)
        .set_label_area_size(LabelAreaPosition::Bottom, 50)
        .build_cartesian_2d(
            -0.5f64..(num_groups as f64 - 0.5),
            (y_min..y_max).log_scale(),
        )?;
    chart
        .configure_mesh()
        .x_desc(x_label)
        .y_desc(y_label)
        .x_label_formatter(&|v| {
            let idx = *v as usize;
            if idx < x_labels.len() {
                x_labels[idx].clone()
            } else {
                String::new()
            }
        })
        .draw()?;
    for (si, s) in groups.iter().enumerate() {
        let offset = (si as f64 - (num_series as f64 - 1.0) / 2.0) * bar_width;
        chart.draw_series(s.values.iter().enumerate().map(|(i, &v)| {
            let x = i as f64 + offset;
            Rectangle::new(
                [(x - bar_width / 2.0, 1e-15), (x + bar_width / 2.0, v)],
                s.color.filled(),
            )
        }))?;
    }
    root.present()?;
    Ok(())
}

fn cities_for_distribution(distribution: &str) -> Vec<&'static str> {
    match distribution {
        "solana" => vec![
            "Westpoort",
            "Frankfurt",
            "London",
            "Basel",
            "Secaucus",
            "Los Angeles",
            "Tokyo",
            "Singapore",
            "Cape Town",
            "Buenos Aires",
        ],
        "sui" => vec![
            "Los Angeles",
            "Dublin",
            "London",
            "Paris",
            "Frankfurt",
            "Singapore",
            "Tokyo",
        ],
        "5hubs" => vec!["San Francisco", "Secaucus", "London", "Shanghai", "Tokyo"],
        "stock_exchanges" => vec![
            "Toronto",
            "Secaucus",
            "Westpoort",
            "Taipei",
            "Pune",
            "Shanghai",
            "Hong Kong",
            "Tokyo",
        ],
        _ => vec![],
    }
}

fn city_display_name(city: &str) -> &str {
    match city {
        "Westpoort" => "Amsterdam",
        "Secaucus" => "New York City",
        other => other,
    }
}

pub fn generate_latency_plots(
    distribution: &str,
    sampling: &str,
    data_shreds: usize,
    total_shreds: usize,
) -> Result<()> {
    let dir = output_dir("latency");
    let csv_path = dir.join(format!(
        "{distribution}-{sampling}-{data_shreds}-{total_shreds}.csv"
    ));
    if !csv_path.exists() {
        eprintln!("latency CSV not found: {}", csv_path.display());
        return Ok(());
    }
    let data = CsvData::from_file(&csv_path)?;
    let percentiles = data.column_f64("percentile")?;
    let has_final = data.column_index("final").is_some();
    let has_fast_final = data.column_index("local_fast_final").is_some();
    let has_slow_final = data.column_index("local_slow_final").is_some();
    let has_notar = data.column_index("notar").is_some();
    let has_block = data.column_index("block").is_some();
    let has_rotor = data.column_index("rotor_0").is_some();
    let has_direct = data.column_index("direct_0").is_some();

    if has_final && has_fast_final && has_slow_final {
        let final_vals = data.column_f64("final")?;
        let slow_vals = data.column_f64_or("local_slow_final", 0.0);
        let y_max = final_vals.iter().cloned().fold(0.0f64, f64::max) * 1.15;
        let final_only: Vec<f64> = final_vals
            .iter()
            .zip(slow_vals.iter())
            .map(|(&f, &s)| f - s)
            .collect();
        plot_stacked_bar_linear(
            &dir.join("latency_histogram_final_only.png"),
            "Alpenglow Latency Histogram for Random Leaders",
            "Validators reached [% of stake]",
            "Latency [ms]",
            &percentiles,
            &[
                BarSeries {
                    label: "Slow Finalization",
                    values: slow_vals.clone(),
                    color: MAGENTA,
                },
                BarSeries {
                    label: "Finalization",
                    values: final_only,
                    color: RED,
                },
            ],
            0.0,
            y_max.max(100.0),
        )?;
    }

    if has_notar && has_block {
        let block_vals = data.column_f64("block")?;
        let notar_vals = data.column_f64("notar")?;
        let notar_delta: Vec<f64> = notar_vals
            .iter()
            .zip(block_vals.iter())
            .map(|(&n, &b)| (n - b).max(0.0))
            .collect();
        if has_final {
            let final_vals = data.column_f64("final")?;
            let final_delta: Vec<f64> = final_vals
                .iter()
                .zip(notar_vals.iter())
                .map(|(&f, &n)| (f - n).max(0.0))
                .collect();
            let y_max = final_vals.iter().cloned().fold(0.0f64, f64::max) * 1.15;
            plot_stacked_bar_linear(
                &dir.join("latency_histogram.png"),
                "Latency Histogram for Random Leaders",
                "Validators reached [% of stake]",
                "Latency [ms]",
                &percentiles,
                &[
                    BarSeries {
                        label: "Block",
                        values: block_vals.clone(),
                        color: BLUE,
                    },
                    BarSeries {
                        label: "Notarization",
                        values: notar_delta,
                        color: GREEN,
                    },
                    BarSeries {
                        label: "Finalization",
                        values: final_delta,
                        color: RED,
                    },
                ],
                0.0,
                y_max.max(100.0),
            )?;
        }
        if has_rotor && has_direct {
            let rotor_vals = data.column_f64("rotor_0")?;
            let direct_vals = data.column_f64("direct_0")?;
            let rotor_delta: Vec<f64> = rotor_vals
                .iter()
                .zip(direct_vals.iter())
                .map(|(&r, &d)| (r - d).max(0.0))
                .collect();
            let y_max = rotor_vals.iter().cloned().fold(0.0f64, f64::max) * 1.15;
            plot_stacked_bar_linear(
                &dir.join("latency_histogram_rotor.png"),
                &format!("Rotor Latency Histogram (gamma = {data_shreds}, Gamma = {total_shreds})"),
                "Validators reached [% of stake]",
                "Latency [ms]",
                &percentiles,
                &[
                    BarSeries {
                        label: "Network Latency",
                        values: direct_vals,
                        color: BLUE,
                    },
                    BarSeries {
                        label: "Rotor",
                        values: rotor_delta,
                        color: ORANGE,
                    },
                ],
                0.0,
                y_max.max(100.0),
            )?;
        }
    }
    Ok(())
}

pub fn generate_city_latency_plots(
    distribution: &str,
    sampling: &str,
    data_shreds: usize,
    total_shreds: usize,
) -> Result<()> {
    let cities = cities_for_distribution(distribution);
    for city in &cities {
        let city_dir = output_dir("latency").join(city);
        let csv_path = city_dir.join(format!(
            "{distribution}-{sampling}-{data_shreds}-{total_shreds}.csv"
        ));
        if !csv_path.exists() {
            continue;
        }
        let data = CsvData::from_file(&csv_path)?;
        let percentiles = data.column_f64("percentile")?;
        let has_block = data.column_index("block").is_some();
        let has_notar = data.column_index("notar").is_some();
        let has_final = data.column_index("final").is_some();
        if has_block && has_notar && has_final {
            let block_vals = data.column_f64("block")?;
            let notar_vals = data.column_f64("notar")?;
            let final_vals = data.column_f64("final")?;
            let notar_delta: Vec<f64> = notar_vals
                .iter()
                .zip(block_vals.iter())
                .map(|(&n, &b)| (n - b).max(0.0))
                .collect();
            let final_delta: Vec<f64> = final_vals
                .iter()
                .zip(notar_vals.iter())
                .map(|(&f, &n)| (f - n).max(0.0))
                .collect();
            let y_max = final_vals.iter().cloned().fold(0.0f64, f64::max) * 1.15;
            let cityname = city_display_name(city);
            plot_stacked_bar_linear(
                &output_dir("latency").join(format!(
                    "latency_histogram_{}.png",
                    cityname.to_lowercase().replace(' ', "_")
                )),
                &format!("Alpenglow Latency Histogram for Leader in {cityname}"),
                "Validators reached [% of stake]",
                "Latency [ms]",
                &percentiles,
                &[
                    BarSeries {
                        label: "Block",
                        values: block_vals,
                        color: BLUE,
                    },
                    BarSeries {
                        label: "Notarization",
                        values: notar_delta,
                        color: GREEN,
                    },
                    BarSeries {
                        label: "Finalization",
                        values: final_delta,
                        color: RED,
                    },
                ],
                0.0,
                y_max.max(100.0),
            )?;
        }
    }
    Ok(())
}

pub fn generate_bandwidth_plots(
    distribution: &str,
    sampling_strat: &str,
    total_shreds: usize,
    max_bandwidth: u64,
) -> Result<()> {
    let dir = output_dir("bandwidth");
    let csv_path = dir.join("bandwidth_usage.csv");
    if !csv_path.exists() {
        eprintln!("bandwidth CSV not found: {}", csv_path.display());
        return Ok(());
    }
    let data = CsvData::from_file(&csv_path)?;
    let mut filtered_rows: Vec<usize> = Vec::new();
    for (i, row) in data.rows.iter().enumerate() {
        let dist = row[0].trim();
        let strat = row[1].trim();
        let ts: usize = row[3].trim().parse().unwrap_or(0);
        let mb: u64 = row[2].trim().parse().unwrap_or(0);
        if dist == distribution
            && strat == sampling_strat
            && ts == total_shreds
            && mb == max_bandwidth
        {
            filtered_rows.push(i);
        }
    }
    if filtered_rows.is_empty() {
        eprintln!(
            "no bandwidth data found for {distribution}/{sampling_strat}/{total_shreds}/{max_bandwidth}"
        );
        return Ok(());
    }
    let goodput_mbps = (max_bandwidth / 2) as f64 / 1e6;
    let validators: Vec<f64> = filtered_rows
        .iter()
        .map(|&i| data.rows[i][4].trim().parse::<f64>().unwrap_or(0.0))
        .collect();
    let rotor_vals: Vec<f64> = filtered_rows
        .iter()
        .map(|&i| data.rows[i][6].trim().parse::<f64>().unwrap_or(0.0) / 1e6)
        .collect();
    let has_voting = data.column_index("voting").is_some();
    let voting_vals: Vec<f64> = if has_voting {
        filtered_rows
            .iter()
            .map(|&i| data.rows[i][5].trim().parse::<f64>().unwrap_or(0.0) / 1e6)
            .collect()
    } else {
        vec![0.0; filtered_rows.len()]
    };
    let max_bw = rotor_vals.iter().cloned().fold(0.0f64, f64::max) * 1.15;
    if has_voting {
        plot_stacked_bar_log_y(
            &dir.join("bandwidth.png"),
            &format!("Up-Bandwidth Usage Histogram for {goodput_mbps:.0} Mbps Goodput"),
            "Validators",
            "Bandwidth [Mbps]",
            &validators,
            &[
                BarSeries {
                    label: "Avg. Rotor",
                    values: rotor_vals.clone(),
                    color: BLUE,
                },
                BarSeries {
                    label: "Voting",
                    values: voting_vals,
                    color: RED,
                },
            ],
            10.0,
            max_bw.max(1000.0),
        )?;
    }
    Ok(())
}

pub fn generate_safety_plots() -> Result<()> {
    let dir = output_dir("safety");
    let expansions = [(32u64, 64u64), (32, 80), (32, 96)];
    let total_shreds_configs = [(32u64, 64u64), (64, 128), (128, 256)];
    let adversary_strengths = [0.4f64, 0.3, 0.2];

    if let Ok(data) = load_safety_data(
        &dir.join("safety_data_expansion_2.csv"),
        "solana",
        &["fa1_partition", "fa1_iid", "stake_weighted", "turbine"],
    ) {
        let df_crash = filter_safety(&data, None, Some(32), None, Some(0.4));
        if !df_crash.is_empty() {
            let x_labels: Vec<String> = expansions.iter().map(|&(_d, t)| format!("{t}")).collect();
            let strategies = ["PS-P", "FA1-IID", "Stake-weighted", "Turbine"];
            let strat_keys = ["fa1_partition", "fa1_iid", "stake_weighted", "turbine"];
            let mut groups = Vec::new();
            for (si, &key) in strat_keys.iter().enumerate() {
                let mut vals = Vec::new();
                for &(d, t) in &expansions {
                    let entry = df_crash.iter().find(|r| {
                        r.sampling_strat == key
                            && r.data_shreds == Some(d)
                            && r.total_shreds == Some(t)
                    });
                    vals.push(entry.map(|e| e.failure_prob).unwrap_or(1e-15));
                }
                groups.push(BarSeries {
                    label: strategies[si],
                    values: vals,
                    color: chart_color(si),
                });
            }
            plot_grouped_bar_log(
                &dir.join("data_expansion_crash.png"),
                "40% Crashes (gamma = 32)",
                "Total shreds (Gamma)",
                "Failure probability",
                &x_labels,
                &groups,
                1e-12,
                1.0,
            )?;
        }
    }

    if let Ok(data) = load_safety_data(
        &dir.join("safety_total_shreds_2.csv"),
        "solana",
        &["fa1_partition", "fa1_iid", "stake_weighted", "turbine"],
    ) {
        let df_crash = filter_safety(&data, None, None, None, Some(0.4));
        let df_ratio: Vec<_> = df_crash
            .iter()
            .filter(|r| {
                if let (Some(d), Some(t)) = (r.data_shreds, r.total_shreds) {
                    t as f64 / d as f64 == 2.0
                } else {
                    false
                }
            })
            .collect();
        if !df_ratio.is_empty() {
            let x_labels: Vec<String> = total_shreds_configs
                .iter()
                .map(|&(_d, t)| format!("{t}"))
                .collect();
            let strategies = ["PS-P", "FA1-IID", "Stake-weighted", "Turbine"];
            let strat_keys = ["fa1_partition", "fa1_iid", "stake_weighted", "turbine"];
            let mut groups = Vec::new();
            for (si, &key) in strat_keys.iter().enumerate() {
                let mut vals = Vec::new();
                for &(d, t) in &total_shreds_configs {
                    let entry = df_ratio.iter().find(|r| {
                        r.sampling_strat == key
                            && r.data_shreds == Some(d)
                            && r.total_shreds == Some(t)
                    });
                    vals.push(entry.map(|e| e.failure_prob).unwrap_or(1e-15));
                }
                groups.push(BarSeries {
                    label: strategies[si],
                    values: vals,
                    color: chart_color(si),
                });
            }
            plot_grouped_bar_log(
                &dir.join("total_shreds.png"),
                "40% Crashes (kappa = 2)",
                "Total shreds (Gamma)",
                "Failure probability",
                &x_labels,
                &groups,
                1e-12,
                1.0,
            )?;
        }
    }

    if let Ok(data) = load_safety_data(
        &dir.join("safety_adversary.csv"),
        "solana",
        &["fa1_partition", "fa1_iid", "stake_weighted", "turbine"],
    ) {
        let strategies = ["PS-P", "FA1-IID", "Stake-weighted", "Turbine"];
        let strat_keys = ["fa1_partition", "fa1_iid", "stake_weighted", "turbine"];
        let x_labels: Vec<String> = adversary_strengths
            .iter()
            .map(|a| format!("{}%", (a * 100.0) as i32))
            .collect();
        let mut groups = Vec::new();
        for (si, &key) in strat_keys.iter().enumerate() {
            let vals: Vec<f64> = adversary_strengths
                .iter()
                .map(|&adv| {
                    let entry = data
                        .iter()
                        .find(|r| r.sampling_strat == key && (r.crashed - adv).abs() < 0.001);
                    entry.map(|e| e.failure_prob).unwrap_or(1e-15)
                })
                .collect();
            groups.push(BarSeries {
                label: strategies[si],
                values: vals,
                color: chart_color(si),
            });
        }
        plot_grouped_bar_log(
            &dir.join("adversary.png"),
            "Crashes (gamma = 32, Gamma = 64)",
            "Crashed nodes (by stake)",
            "Failure probability",
            &x_labels,
            &groups,
            1e-12,
            1.0,
        )?;
    }

    Ok(())
}

struct SafetyRow {
    sampling_strat: String,
    data_shreds: Option<u64>,
    total_shreds: Option<u64>,
    crashed: f64,
    byzantine: f64,
    failure_prob: f64,
}

fn load_safety_data(
    path: &Path,
    distribution: &str,
    include_strategies: &[&str],
) -> Result<Vec<SafetyRow>> {
    if !path.exists() {
        return Err(color_eyre::eyre::eyre!(
            "safety CSV not found: {}",
            path.display()
        ));
    }
    let data = CsvData::from_file(path)?;
    let mut rows = Vec::new();
    let dist_idx = data.column_index("stake_distribution");
    let strat_idx = data.column_index("sampling_strat");
    let crash_idx = data
        .column_index("crashed")
        .or(data.column_index("adversary"));
    let byz_idx = data.column_index("byzantine");
    let ds_idx = data.column_index("data_shreds");
    let ts_idx = data.column_index("total_shreds");
    let skip_headers = [
        "stake_distribution",
        "sampling_strat",
        "data_shreds",
        "total_shreds",
        "byzantine",
        "crashed",
        "adversary",
    ];
    for row in &data.rows {
        let dist = dist_idx.map_or("", |i| row[i].trim());
        if dist != distribution {
            continue;
        }
        let strat = strat_idx.map_or("", |i| row[i].trim());
        if !include_strategies.contains(&strat) {
            continue;
        }
        let data_shreds = ds_idx.and_then(|i| row[i].trim().parse::<u64>().ok());
        let total_shreds = ts_idx.and_then(|i| row[i].trim().parse::<u64>().ok());
        let crashed = crash_idx
            .and_then(|i| row[i].trim().parse::<f64>().ok())
            .unwrap_or(0.0);
        let byzantine = byz_idx
            .and_then(|i| row[i].trim().parse::<f64>().ok())
            .unwrap_or(0.0);
        let mut max_failure = 0.0f64;
        for (col_idx, header) in data.headers.iter().enumerate() {
            let h = header.trim();
            if skip_headers.contains(&h) {
                continue;
            }
            if let Ok(val) = row[col_idx].trim().parse::<f64>() {
                let prob = 2f64.powf(val);
                if prob > max_failure {
                    max_failure = prob;
                }
            }
        }
        rows.push(SafetyRow {
            sampling_strat: strat.to_string(),
            data_shreds,
            total_shreds,
            crashed,
            byzantine,
            failure_prob: max_failure,
        });
    }
    Ok(rows)
}

fn filter_safety<'a>(
    data: &'a [SafetyRow],
    total_shreds: Option<u64>,
    data_shreds: Option<u64>,
    adversary: Option<f64>,
    crashed: Option<f64>,
) -> Vec<&'a SafetyRow> {
    data.iter()
        .filter(|r| {
            if let Some(ts) = total_shreds {
                if r.total_shreds != Some(ts) {
                    return false;
                }
            }
            if let Some(ds) = data_shreds {
                if r.data_shreds != Some(ds) {
                    return false;
                }
            }
            if let Some(adv) = adversary {
                if (r.byzantine - adv).abs() > 0.001 {
                    return false;
                }
            }
            if let Some(cr) = crashed {
                if (r.crashed - cr).abs() > 0.001 {
                    return false;
                }
            }
            true
        })
        .collect()
}

pub fn generate_all_plots(
    distribution: &str,
    sampling: &str,
    data_shreds: usize,
    total_shreds: usize,
) {
    if let Err(e) = generate_latency_plots(distribution, sampling, data_shreds, total_shreds) {
        eprintln!("failed to generate latency plots: {e}");
    }
    if let Err(e) = generate_city_latency_plots(distribution, sampling, data_shreds, total_shreds) {
        eprintln!("failed to generate city latency plots: {e}");
    }
    if let Err(e) = generate_bandwidth_plots(distribution, sampling, total_shreds, 1_000_000_000) {
        eprintln!("failed to generate bandwidth plots: {e}");
    }
    if let Err(e) = generate_safety_plots() {
        eprintln!("failed to generate safety plots: {e}");
    }
}
