# Copyright (c) Anza Technology, Inc.
# SPDX-License-Identifier: Apache-2.0

import matplotlib.pyplot as plt
import numpy as np
import pandas as pd

LATENCY_DATA_EXPANSION_PLOTS = False
LATENCY_TOTAL_SHREDS_PLOTS = False
SAFETY_DATA_EXPANSION_PLOTS = True
SAFETY_TOTAL_SHREDS_PLOTS = True
SAFETY_ADVERSARY_PLOTS = True

# Stake distribution to use in the underlying dataset.
# Currently available: solana, sui, 5hubs, stock_exchanges
STAKE_DISTRIBUTION = "solana"
# Sampling strategy to use in the underlying dataset.
SAMPLING_STRATS = ["uniform", "stake_weighted", "fa1_iid", "fa1_partition", "turbine"]
# Numbers of data/total shreds to use for data expansion ratio comparison.
EXPANSION_RATIO = [(32, 64), (32, 80), (32, 96), (32, 320)]
# Numbers of data/total shreds to use for total shreds comparison.
# TOTAL_SHREDS = [(32, 64), (64, 128), (128, 256), (256, 512)]
TOTAL_SHREDS = [(32, 64), (64, 128), (128, 256)]


def metric_word(metric):
    metric_word = ""
    if metric == "direct":
        metric_word = "Direct Network"
    elif metric == "rotor":
        metric_word = "Rotor"
    elif metric == "notar":
        metric_word = "Notarization"
    elif metric == "final":
        metric_word = "Finalization"
    elif metric == "fast_final":
        metric_word = "Fast-Finalization"
    elif metric == "slow_final":
        metric_word = "Slow-Finalization"
    return metric_word


# general plotting style settings
plt.rc("axes", axisbelow=True)
plt.rcParams.update({"font.size": 14, "axes.titlesize": 18, "axes.labelsize": 16})
plt.style.use("fivethirtyeight")

if LATENCY_DATA_EXPANSION_PLOTS:
    # load data frames for different sampling strategies and expansion ratios from CSV
    dfs = []
    for sampling in SAMPLING_STRATS:
        for data_shreds, total_shreds in EXPANSION_RATIO:
            file_path = f"./data/output/simulations/latency/{STAKE_DISTRIBUTION}-{sampling}-{data_shreds}-{total_shreds}.csv"
            dfs.append(pd.read_csv(file_path))
            dfs[-1]["sampling_strat"] = sampling
            dfs[-1]["data_shreds"] = data_shreds
            dfs[-1]["total_shreds"] = total_shreds
    df = pd.concat(dfs)

    # plot MEDIAN finalization time for different expansion ratios (only for FA1)
    df_median = df[df["percentile"] == 50]
    df_median = df_median[df_median["sampling_strat"] == "fa1"]
    avg_direct = df_median["direct"].mean()
    fig = plt.figure(figsize=(6, 6))
    fig.patch.set_facecolor("white")
    fig.gca().set_facecolor("white")
    w, x = 0.8, np.arange(len(EXPANSION_RATIO))
    # for metric in ['final', 'rotor']:
    #     plt.bar(x, df[metric], width=w, label=metric_word(metric))
    plt.bar(x, df_median["rotor"], width=w)

    plt.gca().set_xticks(x)
    plt.gca().set_xticklabels([t for (d, t) in EXPANSION_RATIO])
    plt.title(f"Median Rotor Latency ($\\gamma = 32$)")
    plt.xlabel("Total shreds ($\\Gamma$)")
    plt.ylabel("Latency [ms]")
    plt.ylim(0, 120)
    plt.axhline(y=avg_direct, color="r", linestyle="--")
    plt.grid(True, axis="y", linestyle="--", alpha=0.7)
    plt.tight_layout()
    plt.savefig(f"./data/output/simulations/latency/data_expansion_median.png", dpi=300)

    # plot average finalization time for different expansion ratios (only for FA1)
    df_max = df[df["percentile"] == 100]
    df_max = df_max[df_max["sampling_strat"] == "fa1"]
    avg_direct = df_max["direct"].mean()
    fig = plt.figure(figsize=(12, 7))
    fig.patch.set_facecolor("white")
    fig.gca().set_facecolor("white")
    w, x = 0.8, np.arange(len(EXPANSION_RATIO))
    # for metric in ['final', 'rotor']:
    #     plt.bar(x, df[metric], width=w, label=metric_word(metric))
    plt.bar(x, df_max["rotor"], width=w)

    plt.gca().set_xticks(x)
    plt.gca().set_xticklabels([t for (d, t) in EXPANSION_RATIO])
    plt.title(f"Average Rotor Latency with 32 Data Shreds")
    plt.xlabel("Total shreds ($\\Gamma$)")
    plt.ylabel("Latency [ms]")
    plt.axhline(y=avg_direct, color="r", linestyle="--")
    plt.grid(True, axis="y", linestyle="--", alpha=0.7)
    plt.tight_layout()
    plt.savefig(f"./data/output/simulations/latency/data_expansion_max.png", dpi=300)

    df = df.groupby(["sampling_strat", "data_shreds", "total_shreds"])[
        ["direct", "rotor", "final"]
    ].mean()
    df = df.reset_index()

    # plot average finalization time for different expansion ratios (and sampling strategies)
    for metric in ["rotor", "final"]:
        fig = plt.figure(figsize=(12, 7))
        fig.patch.set_facecolor("white")
        fig.gca().set_facecolor("white")
        w, x = 0.2, np.arange(len(EXPANSION_RATIO))
        df_uniform = df[df["sampling_strat"] == "uniform"]
        df_stake_weighted = df[df["sampling_strat"] == "stake_weighted"]
        df_fa1 = df[df["sampling_strat"] == "fa1"]
        df_turbine = df[df["sampling_strat"] == "turbine"]
        plt.bar(x - 1.5 * w, df_uniform[metric], width=w, label="Uniform")
        plt.bar(x - 0.5 * w, df_stake_weighted[metric], width=w, label="Stake-weighted")
        plt.bar(x + 0.5 * w, df_fa1[metric], width=w, label="FA1")
        plt.bar(x + 1.5 * w, df_turbine[metric], width=w, label="Turbine")

        plt.gca().set_xticks(x)
        plt.gca().set_xticklabels([t for (d, t) in EXPANSION_RATIO])
        plt.title(f"Average {metric_word(metric)} Latency with 32 Data Shreds")
        plt.xlabel("Total shreds ($\\Gamma$)")
        plt.ylabel("Latency [ms]")
        plt.legend()
        plt.grid(True, axis="y", linestyle="--", alpha=0.7)
        plt.tight_layout()
        plt.savefig(
            f"./data/output/simulations/latency/data_expansion_{metric}_multi.png",
            dpi=300,
        )

    # plot average finalization time for different expansion ratios (only for FA1)
    df = df[df["sampling_strat"] == "fa1"]
    print(df)
    avg_direct = df["direct"].mean()
    fig = plt.figure(figsize=(6, 6))
    fig.patch.set_facecolor("white")
    fig.gca().set_facecolor("white")
    w, x = 0.8, np.arange(len(EXPANSION_RATIO))
    # for metric in ['final', 'rotor']:
    #     plt.bar(x, df[metric], width=w, label=metric_word(metric))
    plt.bar(x, df["rotor"], width=w)

    plt.gca().set_xticks(x)
    plt.gca().set_xticklabels([t for (d, t) in EXPANSION_RATIO])
    plt.title(f"Average Rotor Latency ($\\gamma = 32$)")
    plt.xlabel("Total shreds ($\\Gamma$)")
    plt.ylabel("Latency [ms]")
    plt.ylim(0, 120)
    plt.axhline(y=avg_direct, color="r", linestyle="--")
    plt.grid(True, axis="y", linestyle="--", alpha=0.7)
    plt.tight_layout()
    plt.savefig(f"./data/output/simulations/latency/data_expansion.png", dpi=300)

if LATENCY_TOTAL_SHREDS_PLOTS:
    # load data frames for different sampling strategies and expansion ratios from CSV
    dfs = []
    for sampling in SAMPLING_STRATS:
        for data_shreds, total_shreds in TOTAL_SHREDS:
            file_path = f"./data/output/simulations/latency/{STAKE_DISTRIBUTION}-{sampling}-{data_shreds}-{total_shreds}.csv"
            dfs.append(pd.read_csv(file_path))
            dfs[-1]["sampling_strat"] = sampling
            dfs[-1]["data_shreds"] = data_shreds
            dfs[-1]["total_shreds"] = total_shreds
    df = pd.concat(dfs)
    df = df.groupby(["sampling_strat", "data_shreds", "total_shreds"])[
        ["rotor", "final"]
    ].mean()
    df = df.reset_index()

    # plot average finalization time for different total shreds (and sampling strategies)
    # all with data expansion ratio of 2
    for metric in ["rotor", "final"]:
        fig = plt.figure(figsize=(12, 7))
        fig.patch.set_facecolor("white")
        fig.gca().set_facecolor("white")
        w, x = 0.2, np.arange(len(TOTAL_SHREDS))
        df_uniform = df[df["sampling_strat"] == "uniform"]
        df_stake_weighted = df[df["sampling_strat"] == "stake_weighted"]
        df_fa1 = df[df["sampling_strat"] == "fa1"]
        df_turbine = df[df["sampling_strat"] == "turbine"]
        plt.bar(x - 1.5 * w, df_uniform[metric], width=w, label="Uniform")
        plt.bar(x - 0.5 * w, df_stake_weighted[metric], width=w, label="Stake-weighted")
        plt.bar(x + 0.5 * w, df_fa1[metric], width=w, label="FA1")
        plt.bar(x + 1.5 * w, df_turbine[metric], width=w, label="Turbine")

        plt.gca().set_xticks(x)
        plt.gca().set_xticklabels([t for (d, t) in TOTAL_SHREDS])
        plt.title(f"Average {metric_word(metric)} Latency with Data Expansion Ratio 2")
        plt.xlabel("Total shreds ($\\Gamma$)")
        plt.ylabel("Latency [ms]")
        plt.legend()
        plt.grid(True, axis="y", linestyle="--", alpha=0.7)
        plt.tight_layout()
        plt.savefig(
            f"./data/output/simulations/latency/total_shreds_{metric}.png", dpi=300
        )

EXPANSION_RATIO = [(32, 64), (32, 80), (32, 96)]

if SAFETY_DATA_EXPANSION_PLOTS:
    # load safety test data from CSV
    file_path = "./data/output/simulations/safety/safety_data_expansion_2.csv"
    df = pd.read_csv(file_path)
    df = df[df["stake_distribution"] == STAKE_DISTRIBUTION]
    df = df[df["sampling_strat"] != "uniform"]
    df_expansion = df[df["data_shreds"] == 32]
    df_expansion_crash = df_expansion[df_expansion["adversary"] == 0.4]
    df_expansion_byz = df_expansion[df_expansion["adversary"] == 0.2]

    # # plot crash safety vs Byzantine attack safety for different data expansion ratios
    # fig = plt.figure(figsize=(6, 6))
    # fig.patch.set_facecolor('white')
    # fig.gca().set_facecolor('white')
    # w, x = 0.4, np.arange(len(EXPANSION_RATIO))
    # df = df_expansion
    # df['failure_prob'] = df['safety'].apply(lambda x: 2**x)
    # df_stake_weighted = df[df['sampling_strat'] == 'fa1']
    # df_crash = df_stake_weighted[df_stake_weighted['adversary'] == 0.4]
    # df_byz = df_stake_weighted[df_stake_weighted['adversary'] == 0.2]
    # plt.bar(x - 0.5 * w, df_crash['failure_prob'], width=w, label='Crash Failure')
    # plt.bar(x + 0.5 * w, df_byz['failure_prob'], width=w, label='Equivocation Attack')
    #
    # plt.gca().set_xticks(x)
    # plt.gca().set_xticklabels([t for (d, t) in EXPANSION_RATIO])
    # plt.title(f'Failure Probabilities ($\\gamma = 32$)')
    # plt.xlabel('Total shreds ($\\Gamma$)')
    # plt.ylabel('Failure probability')
    # plt.yscale('log')
    # plt.ylim(1e-10, 1)
    # plt.legend(loc='lower left')
    # plt.legend()
    # plt.grid(True, axis='y', linestyle='--', alpha=0.7)
    # plt.tight_layout()
    # plt.savefig(f'./data/output/simulations/safety/data_expansion_crash_v_byz.png', dpi=300)

    # plot crash safety for different data expansion ratios (with 32 data shreds)
    fig = plt.figure(figsize=(6, 6))
    fig.patch.set_facecolor("white")
    fig.gca().set_facecolor("white")
    w, x = 0.225, np.arange(len(EXPANSION_RATIO))
    df = df_expansion_crash
    df["failure_prob"] = df["safety"].apply(lambda x: 2**x)
    df_stake_weighted = df[df["sampling_strat"] == "stake_weighted"]
    df_ours = df[df["sampling_strat"] == "fa1_partition"]
    df_fa1 = df[df["sampling_strat"] == "fa1_iid"]
    df_turbine = df[df["sampling_strat"] == "turbine"]
    plt.bar(x - 1.5 * w, df_ours["failure_prob"], width=w, label="PS-P")
    plt.bar(x - 0.5 * w, df_fa1["failure_prob"], width=w, label="FA1-IID")
    plt.bar(
        x + 0.5 * w, df_stake_weighted["failure_prob"], width=w, label="Stake-weighted"
    )
    plt.bar(x + 1.5 * w, df_turbine["failure_prob"], width=w, label="Turbine")

    plt.gca().set_xticks(x)
    plt.gca().set_xticklabels([t for (d, t) in EXPANSION_RATIO])
    plt.title(f"40% Crashes ($\\gamma = 32$)")
    plt.xlabel("Total shreds ($\\Gamma$)")
    plt.ylabel("Failure probability")
    plt.yscale("log")
    plt.ylim(1e-12, 1)
    plt.legend(loc="lower left")
    plt.grid(True, axis="y", linestyle="--", alpha=0.7)
    plt.tight_layout()
    plt.savefig(f"./data/output/simulations/safety/data_expansion_crash.png", dpi=300)

    # # plot Byzantine attack safety for different data expansion ratios (with 32 data shreds)
    # fig = plt.figure(figsize=(12, 7))
    # fig.patch.set_facecolor('white')
    # fig.gca().set_facecolor('white')
    # w, x = 0.225, np.arange(len(EXPANSION_RATIO))
    # df = df_expansion_byz
    # df['failure_prob'] = df['safety'].apply(lambda x: 2**x)
    # df_stake_weighted = df[df['sampling_strat'] == 'stake_weighted']
    # df_ours = df[df['sampling_strat'] == 'fa1_partition']
    # df_fa1 = df[df['sampling_strat'] == 'fa1_iid']
    # df_turbine = df[df['sampling_strat'] == 'turbine']
    # plt.bar(x - 1.5 * w, df_ours['failure_prob'], width=w, label='PS-P')
    # plt.bar(x - 0.5 * w, df_fa1['failure_prob'], width=w, label='FA1-IID')
    # plt.bar(x + 0.5 * w, df_stake_weighted['failure_prob'], width=w, label='Stake-weighted')
    # plt.bar(x + 1.5 * w, df_turbine['failure_prob'], width=w, label='Turbine')
    #
    # plt.gca().set_xticks(x)
    # plt.gca().set_xticklabels([t for (d, t) in EXPANSION_RATIO])
    # plt.title(f'Equivocation Probability for 20% Byzantine with 32 Data Shreds')
    # plt.xlabel('Total shreds ($\\Gamma$)')
    # plt.ylabel('Attack success probability [$log_2$]')
    # plt.legend()
    # plt.grid(True, axis='y', linestyle='--', alpha=0.7)
    # plt.tight_layout()
    # plt.savefig(f'./data/output/simulations/safety/data_expansion_byz.png', dpi=300)

if SAFETY_TOTAL_SHREDS_PLOTS:
    # load safety test data from CSV
    file_path = "./data/output/simulations/safety/safety_total_shreds_2.csv"
    df = pd.read_csv(file_path)
    df = df[df["stake_distribution"] == STAKE_DISTRIBUTION]
    df = df[df["sampling_strat"] != "uniform"]
    df_total = df[df["total_shreds"] / df["data_shreds"] == 2]
    df_total_crash = df_total[df_total["adversary"] == 0.4]
    df_total_byz = df_total[df_total["adversary"] == 0.2]

    # plot crash safety for different total shreds (all with data expanision ratio 2)
    fig = plt.figure(figsize=(6, 6))
    fig.patch.set_facecolor("white")
    fig.gca().set_facecolor("white")
    w, x = 0.225, np.arange(len(TOTAL_SHREDS))
    df = df_total_crash
    df["failure_prob"] = df["safety"].apply(lambda x: 2**x)
    df_ours = df[df["sampling_strat"] == "fa1_partition"]
    df_fa1 = df[df["sampling_strat"] == "fa1_iid"]
    df_stake_weighted = df[df["sampling_strat"] == "stake_weighted"]
    df_turbine = df[df["sampling_strat"] == "turbine"]
    plt.bar(x - 1.5 * w, df_ours["failure_prob"], width=w, label="PS-P")
    plt.bar(x - 0.5 * w, df_fa1["failure_prob"], width=w, label="FA1-IID")
    plt.bar(
        x + 0.5 * w, df_stake_weighted["failure_prob"], width=w, label="Stake-weighted"
    )
    plt.bar(x + 1.5 * w, df_turbine["failure_prob"], width=w, label="Turbine")

    plt.gca().set_xticks(x)
    plt.gca().set_xticklabels([t for (d, t) in TOTAL_SHREDS])
    plt.title(f"40% Crashes ($\\kappa = 2$)")
    plt.xlabel("Total shreds ($\\Gamma$)")
    plt.ylabel("Failure probability")
    plt.yscale("log")
    plt.ylim(1e-12, 1)
    plt.legend(loc="lower left")
    plt.grid(True, axis="y", linestyle="--", alpha=0.7)
    plt.tight_layout()
    plt.savefig(f"./data/output/simulations/safety/total_shreds.png", dpi=300)

if SAFETY_ADVERSARY_PLOTS:
    # load safety test data from CSV
    file_path = "./data/output/simulations/safety/safety_adversary.csv"
    df = pd.read_csv(file_path)
    df = df[df["stake_distribution"] == STAKE_DISTRIBUTION]

    # plot crash safety for different total shreds (all with data expanision ratio 2)
    fig = plt.figure(figsize=(6, 6))
    fig.patch.set_facecolor("white")
    fig.gca().set_facecolor("white")
    w, x = 0.225, np.arange(3)
    df["failure_prob"] = df["safety"].apply(lambda x: 2**x)
    df_ours = df[df["sampling_strat"] == "fa1_partition"]
    df_fa1 = df[df["sampling_strat"] == "fa1_iid"]
    df_stake_weighted = df[df["sampling_strat"] == "stake_weighted"]
    df_turbine = df[df["sampling_strat"] == "turbine"]
    plt.bar(x - 1.5 * w, df_ours["failure_prob"], width=w, label="PS-P")
    plt.bar(x - 0.5 * w, df_fa1["failure_prob"], width=w, label="FA1-IID")
    plt.bar(
        x + 0.5 * w, df_stake_weighted["failure_prob"], width=w, label="Stake-weighted"
    )
    plt.bar(x + 1.5 * w, df_turbine["failure_prob"], width=w, label="Turbine")

    plt.gca().set_xticks(x)
    plt.gca().set_xticklabels(["40%", "30%", "20%"])
    plt.title(f"Crashes ($\\gamma = 32, \\Gamma = 64$)")
    plt.xlabel("Crashed nodes (by stake)")
    plt.ylabel("Failure probability")
    plt.yscale("log")
    plt.ylim(1e-12, 1)
    plt.legend(loc="lower left")
    plt.grid(True, axis="y", linestyle="--", alpha=0.7)
    plt.tight_layout()
    plt.savefig(f"./data/output/simulations/safety/adversary.png", dpi=300)
