# Copyright (c) Anza Technology, Inc.
# SPDX-License-Identifier: Apache-2.0

import pandas as pd
import matplotlib.pyplot as plt

# Stake distribution to use in the underlying dataset.
# Currently available: solana, sui, 5hubs, stock_exchanges
STAKE_DISTRIBUTION = 'stock_exchanges'
# Sampling strategy to use in the underlying dataset.
# Currently available: uniform, stake_weighted, fa1, turbine, decaying_acceptance
SAMPLING = 'stake_weighted'
# Number of data/total shreds to use in the underlying dataset.
# Currently available combinations: 32/64, 32/80, 32/96, 32/320, 64/128, 128/256, 256/512
DATA_SHREDS = 32
TOTAL_SHREDS = 64

CITIES = []
if STAKE_DISTRIBUTION == 'solana':
    CITIES = [
        'Westpoort',
        'Frankfurt',
        'London',
        'Zurich',
        'New York City',
        'Los Angeles',
        'Tokyo',
        'Singapore',
        'Cape Town',
        'Buenos Aires',
    ]
elif STAKE_DISTRIBUTION == 'sui':
    CITIES = [
        'Los Angeles',
        'Dublin',
        'London',
        'Paris',
        'Frankfurt',
        'Singapore',
        'Tokyo',
    ]
elif STAKE_DISTRIBUTION == '5hubs':
    CITIES = [
        'San Francisco',
        'New York City',
        'London',
        'Shanghai',
        'Tokyo',
    ]

def city_name_to_print(city):
    if city == 'Westpoort':
        return 'Amsterdam'
    else:
        return city

# general plotting style settings
plt.rc('axes', axisbelow=True)
plt.rcParams.update({'font.size': 14, 'axes.titlesize': 18, 'axes.labelsize': 16})
plt.style.use('dark_background')

# load data frame from CSV
file_path = f'./data/output/simulations/latency/{STAKE_DISTRIBUTION}-{SAMPLING}-{DATA_SHREDS}-{TOTAL_SHREDS}.csv'
df = pd.read_csv(file_path)

# print average finalization latencies
print('final', df['final'].mean())
print('fast final', df['fast_final'].mean())
print('slow final', df['slow_final'].mean())

# average of averages (finalization types only)
plt.figure(figsize=(12, 7))
metrics = ['final', 'slow_final', 'fast_final']
for metric in reversed(metrics):
    plt.bar(df['percentile'], df[metric], label=metric, alpha=0.5)

plt.title(f"Latency Histogram for Random Leaders")
plt.xlabel("validators reached [% of stake]")
plt.ylabel("latency [ms]")
plt.legend()
plt.grid(True, axis='y', linestyle='--', alpha=0.7)
plt.tight_layout()
plt.savefig(f"./data/output/simulations/latency/latency_histogram_final_only.png", dpi=300)

# average of averages (all stages)
plt.figure(figsize=(12, 7))
metrics = ['direct', 'rotor', 'notar', 'final', 'slow_final']
for metric in reversed(metrics):
    plt.bar(df['percentile'], df[metric], label=metric)

plt.title(f"Latency Histogram for Random Leaders")
plt.xlabel("validators reached [% of stake]")
plt.ylabel("latency [ms]")
plt.legend()
plt.grid(True, axis='y', linestyle='--', alpha=0.7)
plt.tight_layout()
plt.savefig(f"./data/output/simulations/latency/latency_histogram.png", dpi=300)

# individual city plots
for city in CITIES:
    file_path = f'./data/output/simulations/latency/{city}/{STAKE_DISTRIBUTION}-{SAMPLING}-{DATA_SHREDS}-{TOTAL_SHREDS}.csv'
    df = pd.read_csv(file_path)

    plt.figure(figsize=(12, 7))
    metrics = ['direct', 'rotor', 'notar', 'final', 'slow_final']
    for metric in reversed(metrics):
        plt.bar(df['percentile'], df[metric], label=metric)

    cityname = city_name_to_print(city)
    plt.title(f"Latency Histogram for Leader in {cityname}")
    plt.xlabel("validators reached [% of stake]")
    plt.ylabel("latency [ms]")
    plt.legend()
    plt.grid(True, axis='y', linestyle='--', alpha=0.7)
    plt.tight_layout()
    city_filename = cityname.lower().replace(" ", "_")
    plt.savefig(f"./data/output/simulations/latency/latency_histogram_{city_filename}.png", dpi=300)

# individual city plots (fancy)
for city in CITIES:
    file_path = f'./data/output/simulations/latency/{city}/{STAKE_DISTRIBUTION}-{SAMPLING}-{DATA_SHREDS}-{TOTAL_SHREDS}.csv'
    df = pd.read_csv(file_path)
    df['percentile'] = df['percentile'] - 0.5

    fig = plt.figure(figsize=(12, 7))
    fig.patch.set_alpha(0.0)
    plt.bar(df['percentile'], df['final'], label='Alpenglow Finalization', color='#00FFA3')
    plt.bar(df['percentile'], df['direct'], label='Direct Network Delay', color='#138BFF')

    cityname = city_name_to_print(city)
    # plt.title(f"Latency Histogram for Leader in {cityname}")
    # plt.xlabel("validators reached [% of stake]")
    # plt.ylabel("latency [ms]")
    # plt.legend()
    plt.grid(True, axis='y', linestyle='--', alpha=0.7)
    plt.tight_layout()
    city_filename = cityname.lower().replace(" ", "_")
    plt.savefig(f"./data/output/simulations/latency/fancy_latency_histogram_{city_filename}.png", dpi=300, transparent=True)
    plt.close()
