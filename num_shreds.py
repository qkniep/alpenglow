# Copyright (c) Anza Technology, Inc.
# SPDX-License-Identifier: Apache-2.0

import matplotlib.pyplot as plt
import numpy as np
import pandas as pd

# Stake distribution to use in the underlying dataset.
# Currently available: solana, sui, 5hubs, stock_exchanges
STAKE_DISTRIBUTION = 'solana'
# Sampling strategy to use in the underlying dataset.
SAMPLING_STRATS = ['uniform', 'stake_weighted', 'fa1', 'turbine'] #, 'decaying_acceptance']
# Numbers of data/total shreds to use for data expansion ratio comparison.
EXPANSION_RATIO = [(32, 64), (32, 80), (32, 96), (32, 128), (32, 192), (32, 256), (32, 320)]
# Numbers of data/total shreds to use for total shreds comparison.
TOTAL_SHREDS = [(32, 64), (64, 128), (128, 256), (256, 512)]

def metric_word(metric):
    metric_word = ''
    if metric == 'direct':
        metric_word = 'Direct Network'
    elif metric == 'rotor':
        metric_word = 'Rotor'
    elif metric == 'notar':
        metric_word = 'Notarization'
    elif metric == 'final':
        metric_word = 'Finalization'
    elif metric == 'fast_final':
        metric_word = 'Fast-Finalization'
    elif metric == 'slow_final':
        metric_word = 'Slow-Finalization'
    return metric_word

# general plotting style settings
plt.rc('axes', axisbelow=True)
plt.rcParams.update({'font.size': 14, 'axes.titlesize': 18, 'axes.labelsize': 16})
plt.style.use('fivethirtyeight')

# load data frames for different sampling strategies and expansion ratios from CSV
dfs = []
for sampling in SAMPLING_STRATS:
    for (data_shreds, total_shreds) in EXPANSION_RATIO:
        file_path = f'./data/output/simulations/latency/{STAKE_DISTRIBUTION}-{sampling}-{data_shreds}-{total_shreds}.csv'
        dfs.append(pd.read_csv(file_path))
        dfs[-1]['sampling_strat'] = sampling
        dfs[-1]['data_shreds'] = data_shreds
        dfs[-1]['total_shreds'] = total_shreds
df = pd.concat(dfs)
df = df.groupby(['sampling_strat', 'data_shreds', 'total_shreds'])[['direct', 'rotor', 'final']].mean()
df = df.reset_index()

# plot average finalization time for different expansion ratios (and sampling strategies)
for metric in ['rotor', 'final']:
    fig = plt.figure(figsize=(12, 7))
    fig.patch.set_facecolor('white')
    fig.gca().set_facecolor('white')
    w, x = 0.2, np.arange(len(EXPANSION_RATIO))
    df_uniform = df[df['sampling_strat'] == 'uniform']
    df_stake_weighted = df[df['sampling_strat'] == 'stake_weighted']
    df_fa1 = df[df['sampling_strat'] == 'fa1']
    df_turbine = df[df['sampling_strat'] == 'turbine']
    plt.bar(x - 1.5 * w, df_uniform[metric], width=w, label='Uniform')
    plt.bar(x - 0.5 * w, df_stake_weighted[metric], width=w, label='Stake-weighted')
    plt.bar(x + 0.5 * w, df_fa1[metric], width=w, label='FA1')
    plt.bar(x + 1.5 * w, df_turbine[metric], width=w, label='Turbine')

    plt.gca().set_xticks(x)
    plt.gca().set_xticklabels([t for (d, t) in EXPANSION_RATIO])
    plt.title(f'Average {metric_word(metric)} Latency with 32 Data Shreds')
    plt.xlabel('Total shreds ($\\Gamma$)')
    plt.ylabel('Latency [ms]')
    plt.legend()
    plt.grid(True, axis='y', linestyle='--', alpha=0.7)
    plt.tight_layout()
    plt.savefig(f'./data/output/simulations/latency/data_expansion_{metric}_multi.png', dpi=300)

# plot average finalization time for different expansion ratios (only for FA1)
df = df[df['sampling_strat'] == 'fa1']
avg_direct = df['direct'].mean()
for metric in ['rotor', 'final']:
    fig = plt.figure(figsize=(12, 7))
    fig.patch.set_facecolor('white')
    fig.gca().set_facecolor('white')
    w, x = 0.8, np.arange(len(EXPANSION_RATIO))
    plt.bar(x, df[metric], width=w)

    plt.gca().set_xticks(x)
    plt.gca().set_xticklabels([t for (d, t) in EXPANSION_RATIO])
    plt.title(f'Average {metric_word(metric)} Latency with 32 Data Shreds')
    plt.xlabel('Total shreds ($\\Gamma$)')
    plt.ylabel('Latency [ms]')
    plt.axhline(y=avg_direct, color='r', linestyle='--')
    plt.grid(True, axis='y', linestyle='--', alpha=0.7)
    plt.tight_layout()
    plt.savefig(f'./data/output/simulations/latency/data_expansion_{metric}.png', dpi=300)

# load data frames for different sampling strategies and expansion ratios from CSV
dfs = []
for sampling in SAMPLING_STRATS:
    for (data_shreds, total_shreds) in TOTAL_SHREDS:
        file_path = f'./data/output/simulations/latency/{STAKE_DISTRIBUTION}-{sampling}-{data_shreds}-{total_shreds}.csv'
        dfs.append(pd.read_csv(file_path))
        dfs[-1]['sampling_strat'] = sampling
        dfs[-1]['data_shreds'] = data_shreds
        dfs[-1]['total_shreds'] = total_shreds
df = pd.concat(dfs)
df = df.groupby(['sampling_strat', 'data_shreds', 'total_shreds'])[['rotor', 'final']].mean()
df = df.reset_index()

# plot average finalization time for different total shreds (and sampling strategies)
# all with data expansion ratio of 2
for metric in ['rotor', 'final']:
    fig = plt.figure(figsize=(12, 7))
    fig.patch.set_facecolor('white')
    fig.gca().set_facecolor('white')
    w, x = 0.2, np.arange(len(TOTAL_SHREDS))
    df_uniform = df[df['sampling_strat'] == 'uniform']
    df_stake_weighted = df[df['sampling_strat'] == 'stake_weighted']
    df_fa1 = df[df['sampling_strat'] == 'fa1']
    df_turbine = df[df['sampling_strat'] == 'turbine']
    plt.bar(x - 1.5 * w, df_uniform[metric], width=w, label='Uniform')
    plt.bar(x - 0.5 * w, df_stake_weighted[metric], width=w, label='Stake-weighted')
    plt.bar(x + 0.5 * w, df_fa1[metric], width=w, label='FA1')
    plt.bar(x + 1.5 * w, df_turbine[metric], width=w, label='Turbine')

    plt.gca().set_xticks(x)
    plt.gca().set_xticklabels([t for (d, t) in TOTAL_SHREDS])
    plt.title(f'Average {metric_word(metric)} Latency with Data Expansion Ratio 2')
    plt.xlabel('Total shreds ($\\Gamma$)')
    plt.ylabel('Latency [ms]')
    plt.legend()
    plt.grid(True, axis='y', linestyle='--', alpha=0.7)
    plt.tight_layout()
    plt.savefig(f'./data/output/simulations/latency/total_shreds_{metric}.png', dpi=300)

EXPANSION_RATIO = [(32, 64), (32, 80), (32, 96), (32, 128)]

# load safety test data from CSV
file_path = './data/output/simulations/safety/safety.csv'
df = pd.read_csv(file_path)
df = df[df['stake_distribution'] == STAKE_DISTRIBUTION]
df = df[df['sampling_strat'] != 'uniform']
df_expansion = df[df['data_shreds'] == 32]
df_expansion_crash = df_expansion[df_expansion['adversary'] == 0.4]
df_expansion_byz = df_expansion[df_expansion['adversary'] == 0.2]
df_total = df[df['total_shreds'] / df['data_shreds'] == 2]
df_total_crash = df_total[df_total['adversary'] == 0.4]
df_total_byz = df_total[df_total['adversary'] == 0.2]

#
fig = plt.figure(figsize=(12, 7))
fig.patch.set_facecolor('white')
fig.gca().set_facecolor('white')
w, x = 0.2, np.arange(len(EXPANSION_RATIO))
df = df_expansion_crash
df_stake_weighted = df[df['sampling_strat'] == 'stake_weighted']
df_fa1 = df[df['sampling_strat'] == 'fa1']
df_turbine = df[df['sampling_strat'] == 'turbine']
plt.bar(x - w, df_stake_weighted['safety'], width=w, label='Stake-weighted')
plt.bar(x, df_fa1['safety'], width=w, label='FA1')
plt.bar(x + w, df_turbine['safety'], width=w, label='Turbine')

plt.gca().set_xticks(x)
plt.gca().set_xticklabels([t for (d, t) in EXPANSION_RATIO])
plt.title(f'Failure Rate for 40% Crashes with 32 Data Shreds')
plt.xlabel('Total shreds ($\\Gamma$)')
plt.ylabel('Failure probability [$log_2$]')
plt.legend()
plt.grid(True, axis='y', linestyle='--', alpha=0.7)
plt.tight_layout()
plt.savefig(f'./data/output/simulations/safety/data_expansion_crash.png', dpi=300)

#
fig = plt.figure(figsize=(12, 7))
fig.patch.set_facecolor('white')
fig.gca().set_facecolor('white')
w, x = 0.2, np.arange(len(EXPANSION_RATIO))
df = df_expansion_byz
df_stake_weighted = df[df['sampling_strat'] == 'stake_weighted']
df_fa1 = df[df['sampling_strat'] == 'fa1']
df_turbine = df[df['sampling_strat'] == 'turbine']
plt.bar(x - w, df_stake_weighted['safety'], width=w, label='Stake-weighted')
plt.bar(x, df_fa1['safety'], width=w, label='FA1')
plt.bar(x + w, df_turbine['safety'], width=w, label='Turbine')

plt.gca().set_xticks(x)
plt.gca().set_xticklabels([t for (d, t) in EXPANSION_RATIO])
plt.title(f'Equivocation Probability for 20% Byzantine with 32 Data Shreds')
plt.xlabel('Total shreds ($\\Gamma$)')
plt.ylabel('Attack success probability [$log_2$]')
plt.legend()
plt.grid(True, axis='y', linestyle='--', alpha=0.7)
plt.tight_layout()
plt.savefig(f'./data/output/simulations/safety/data_expansion_byz.png', dpi=300)

#
fig = plt.figure(figsize=(12, 7))
fig.patch.set_facecolor('white')
fig.gca().set_facecolor('white')
w, x = 0.2, np.arange(len(TOTAL_SHREDS))
df = df_total_crash
df_stake_weighted = df[df['sampling_strat'] == 'stake_weighted']
df_fa1 = df[df['sampling_strat'] == 'fa1']
df_turbine = df[df['sampling_strat'] == 'turbine']
plt.bar(x - w, df_stake_weighted['safety'], width=w, label='Stake-weighted')
plt.bar(x, df_fa1['safety'], width=w, label='FA1')
plt.bar(x + w, df_turbine['safety'], width=w, label='Turbine')

plt.gca().set_xticks(x)
plt.gca().set_xticklabels([t for (d, t) in TOTAL_SHREDS])
plt.title(f'Failure Rate for 40% Crashes with Data Expansion Ratio 2')
plt.xlabel('Total shreds ($\\Gamma$)')
plt.ylabel('Failure probability [$log_2$]')
plt.legend()
plt.grid(True, axis='y', linestyle='--', alpha=0.7)
plt.tight_layout()
plt.savefig(f'./data/output/simulations/safety/total_shreds.png', dpi=300)
