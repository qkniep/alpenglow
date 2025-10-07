# Copyright (c) Anza Technology, Inc.
# SPDX-License-Identifier: Apache-2.0

import matplotlib as mpl
import matplotlib.pyplot as plt
import pandas as pd

# Stake distribution to use in the underlying dataset.
# Currently available: solana, sui, 5hubs, stock_exchanges
STAKE_DISTRIBUTION = "solana"
# Sampling strategy to use in the underlying dataset.
# Currently available: uniform, stake_weighted, fa1_iid, fa1_bin_packing, turbine, decaying_acceptance
SAMPLING = "stake_weighted"
# Number of data/total shreds to use in the underlying dataset.
# Currently available combinations: 32/64, 32/80, 32/96, 32/320, 64/128, 128/256, 256/512
DATA_SHREDS = 32
TOTAL_SHREDS = 64

LABELS = {
    "direct": "Network latency",
    "rotor": "Rotor",
    "notar": "Notarization",
    "final": "Finalization",
    "fast_final": "Fast-finalization",
    "slow_final": "Slow-finalization",
}

CITIES = []
if STAKE_DISTRIBUTION == "solana":
    CITIES = [
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
    ]
elif STAKE_DISTRIBUTION == "sui":
    CITIES = [
        "Los Angeles",
        "Dublin",
        "London",
        "Paris",
        "Frankfurt",
        "Singapore",
        "Tokyo",
    ]
elif STAKE_DISTRIBUTION == "5hubs":
    CITIES = [
        "San Francisco",
        "Secaucus",
        "London",
        "Shanghai",
        "Tokyo",
    ]
elif STAKE_DISTRIBUTION == "stock_exchanges":
    CITIES = [
        "Toronto",
        "Secaucus",
        "Westpoort",
        "Taipei",
        "Pune",
        "Shanghai",
        "Hong Kong",
        "Tokyo",
    ]


def city_name_to_print(city):
    if city == "Westpoort":
        return "Amsterdam"
    elif city == "Secaucus":
        return "New York City"
    else:
        return city


# general plotting style settings
plt.rc("axes", axisbelow=True)
plt.rcParams.update({"font.size": 14, "axes.titlesize": 18, "axes.labelsize": 16})
plt.style.use("fivethirtyeight")

# load data frame from CSV
file_path = f"./data/output/simulations/latency/{STAKE_DISTRIBUTION}-{SAMPLING}-{DATA_SHREDS}-{TOTAL_SHREDS}.csv"
df = pd.read_csv(file_path)

# print average finalization latencies
print("Random Leader")
print("avg. final", df["final"].mean())
print("avg. fast final", df["fast_final"].mean())
print("avg. slow final", df["slow_final"].mean())
print("median final", df["final"].median())
print("WC final", df["final"].max())

# average of averages (finalization types only)
plt.figure(figsize=(12, 7))
metrics = ["final", "slow_final", "fast_final"]
for metric in reversed(metrics):
    plt.bar(df["percentile"], df[metric], label=LABELS[metric], alpha=0.5)

plt.title(f"Alpenglow Latency Histogram for Random Leaders")
plt.xlabel("Validators reached [% of stake]")
plt.ylabel("Latency [ms]")
plt.xlim(0, 101)
plt.legend()
plt.grid(True, axis="y", linestyle="--", alpha=0.7)
plt.tight_layout()
plt.savefig(
    f"./data/output/simulations/latency/latency_histogram_final_only.png", dpi=300
)

# average of averages (all stages)
fig = plt.figure(figsize=(12, 7))
fig.patch.set_facecolor("white")
fig.gca().set_facecolor("white")
metrics = ["direct", "rotor", "notar", "final"]
for metric in reversed(metrics):
    plt.bar(df["percentile"], df[metric], label=LABELS[metric])

plt.title(f"Latency Histogram for Random Leaders")
plt.xlabel("Validators reached [% of stake]")
plt.ylabel("Latency [ms]")
plt.xlim(0, 101)
plt.legend()
plt.grid(True, axis="y", linestyle="--", alpha=0.7)
plt.tight_layout()
plt.savefig(f"./data/output/simulations/latency/latency_histogram.png", dpi=300)

# average of averages (Rotor only)
fig = plt.figure(figsize=(12, 7))
fig.patch.set_facecolor("white")
fig.gca().set_facecolor("white")
metrics = ["direct", "rotor"]
for metric in reversed(metrics):
    plt.bar(df["percentile"], df[metric], label=LABELS[metric])

plt.title(f"Rotor Latency Histogram for Random Leaders ($\\gamma = 32, \\Gamma = 64$)")
plt.xlabel("Validators reached [% of stake]")
plt.ylabel("Latency [ms]")
plt.xlim(0, 101)
plt.legend()
plt.grid(True, axis="y", linestyle="--", alpha=0.7)
plt.tight_layout()
plt.savefig(f"./data/output/simulations/latency/latency_histogram_rotor.png", dpi=300)

# individual city plots
for city in CITIES:
    file_path = f"./data/output/simulations/latency/{city}/{STAKE_DISTRIBUTION}-{SAMPLING}-{DATA_SHREDS}-{TOTAL_SHREDS}.csv"
    df = pd.read_csv(file_path)

    # print average finalization latencies
    print()
    print(f"Leader in {city}")
    print("avg. Rotor", df["rotor"].mean())
    print("median Rotor", df["rotor"].median())
    print("WC Rotor", df["rotor"].max())
    print("avg. final", df["final"].mean())
    print("avg. fast final", df["fast_final"].mean())
    print("avg. slow final", df["slow_final"].mean())
    print("median final", df["final"].median())
    print("WC final", df["final"].max())

    fig = plt.figure(figsize=(12, 7))
    fig.patch.set_facecolor("white")
    fig.gca().set_facecolor("white")
    metrics = ["direct", "rotor", "notar", "final"]
    for metric in reversed(metrics):
        plt.bar(df["percentile"], df[metric], label=LABELS[metric])

    cityname = city_name_to_print(city)
    plt.title(f"Alpenglow Latency Histogram for Leader in {cityname}")
    plt.xlabel("Validators reached [% of stake]")
    plt.ylabel("Latency [ms]")
    plt.xlim(0, 101)
    plt.legend()
    plt.grid(True, axis="y", linestyle="--", alpha=0.7)
    plt.tight_layout()
    city_filename = cityname.lower().replace(" ", "_")
    plt.savefig(
        f"./data/output/simulations/latency/latency_histogram_{city_filename}.png",
        dpi=300,
    )

# individual city plots (fancy)
mpl.rcParams.update(mpl.rcParamsDefault)
plt.style.use("dark_background")
for city in CITIES:
    file_path = f"./data/output/simulations/latency/{city}/{STAKE_DISTRIBUTION}-{SAMPLING}-{DATA_SHREDS}-{TOTAL_SHREDS}.csv"
    df = pd.read_csv(file_path)
    df["percentile"] = df["percentile"] - 0.5

    fig = plt.figure(figsize=(12, 7))
    fig.patch.set_alpha(0.0)
    plt.bar(
        df["percentile"], df["final"], label="Alpenglow Finalization", color="#00FFA3"
    )
    plt.bar(
        df["percentile"], df["direct"], label="Direct Network Delay", color="#138BFF"
    )

    cityname = city_name_to_print(city)
    # plt.title(f'Latency Histogram for Leader in {cityname}')
    # plt.xlabel('Validators reached [% of stake]')
    # plt.ylabel('Latency [ms]')
    # plt.legend()
    plt.grid(True, axis="y", linestyle="--", alpha=0.7)
    plt.tight_layout()
    city_filename = cityname.lower().replace(" ", "_")
    plt.savefig(
        f"./data/output/simulations/latency/fancy_latency_histogram_{city_filename}.png",
        dpi=300,
        transparent=True,
    )
    plt.close()
