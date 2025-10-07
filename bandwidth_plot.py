# Copyright (c) Anza Technology, Inc.
# SPDX-License-Identifier: Apache-2.0

import matplotlib.pyplot as plt
import numpy as np
import pandas as pd

# Stake distribution to use in the underlying dataset.
# Currently available: solana, sui, 5hubs, stock_exchanges
STAKE_DISTRIBUTION = "solana"
# Sampling strategy to use in the underlying dataset.
# Currently available: uniform, stake_weighted, fa1_iid, fa1_bin_packing, turbine, decaying_acceptance
SAMPLING_STRAT = "stake_weighted"
# Number of total shreds to use.
TOTAL_SHREDS = 64
# Maximum bandwidth available (in bits per second).
# Currently available: 100 Mbps, 1 Gbps, 10 Gbps, 100 Gbps
MAX_BANDWIDTH = 1_000_000_000  # 1 Gbps

goodput = MAX_BANDWIDTH / 2
goodput_mbps = goodput / 1e6


def metric_word(metric):
    metric_word = ""
    if metric == "voting":
        metric_word = "Voting"
    elif metric == "avg_rotor":
        metric_word = "Avg. Rotor"
    elif metric == "wc_rotor":
        metric_word = "WC Rotor"
    return metric_word


# general plotting style settings
plt.rc("axes", axisbelow=True)
plt.rcParams.update({"font.size": 14, "axes.titlesize": 18, "axes.labelsize": 16})
plt.style.use("fivethirtyeight")

# load data frame from CSV
file_path = "./data/output/simulations/bandwidth/bandwidth_usage.csv"
df = pd.read_csv(file_path)
df = df[df["stake_distribution"] == STAKE_DISTRIBUTION]
df = df[df["total_shreds"] == TOTAL_SHREDS]
df = df[df["max_bandwidth"] == MAX_BANDWIDTH]
df["voting"] = df["voting"] / 1e6
df["avg_rotor"] = df["avg_rotor"] / 1e6
df_turbine = df[df["sampling_strat"] == "turbine"]
df = df[df["sampling_strat"] == SAMPLING_STRAT]
# df['avg_rotor'] += df['voting']

print(df["avg_rotor"].sum())

# plot bandwidth usage
fig = plt.figure(figsize=(12, 7))
fig.patch.set_facecolor("white")
fig.gca().set_facecolor("white")
metrics = ["voting", "avg_rotor"]
for metric in reversed(metrics):
    metric_label = metric_word(metric)
    if metric == "voting":
        plt.bar(
            df["validator"],
            df[metric],
            bottom=df["avg_rotor"],
            label=metric_label,
            width=10,
        )
    else:
        plt.bar(df["validator"], df[metric], label=metric_label, width=10)

plt.title(f"Up-Bandwidth Usage Histogram for {goodput_mbps:.0f} Mbps Goodput")
plt.xlabel("Validators")
plt.ylabel("Bandwidth [Mbps]")
plt.xlim(-10, 1292)
plt.ylim(10, 40_000)
plt.yscale("log")
plt.legend()
plt.grid(True, axis="y", linestyle="--", alpha=0.7)
plt.tight_layout()
plt.savefig(f"./data/output/simulations/bandwidth/bandwidth.png", dpi=300)

# plot bandwidth usage (compared to turbine)
fig = plt.figure(figsize=(12, 7))
fig.patch.set_facecolor("white")
fig.gca().set_facecolor("white")
plt.bar(df["validator"], df["avg_rotor"], label=SAMPLING_STRAT, alpha=0.5, width=10)
plt.bar(
    df_turbine["validator"],
    df_turbine["avg_rotor"],
    label="Turbine",
    alpha=0.5,
    width=10,
)

plt.title(f"Up-Bandwidth Usage Histogram Compared to Turbine")
plt.xlabel("Validators")
plt.ylabel("Bandwidth [Mbps]")
plt.xlim(-10, 1292)
plt.ylim(10, 40_000)
plt.yscale("log")
plt.legend()
plt.grid(True, axis="y", linestyle="--", alpha=0.7)
plt.tight_layout()
plt.savefig(f"./data/output/simulations/bandwidth/bandwidth_vs_turbine.png", dpi=300)
