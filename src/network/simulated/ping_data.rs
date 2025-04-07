// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;
use std::fs::File;
use std::sync::LazyLock;

use geo::{Distance, Haversine, Point};

static PING_SERVERS: LazyLock<Vec<PingServer>> = LazyLock::new(|| {
    let mut output = Vec::new();
    let file = File::open("data/servers-2020-07-19.csv").unwrap();
    let mut rdr = csv::Reader::from_reader(file);
    for result in rdr.deserialize() {
        let record: PingServer = result.unwrap();
        output.push(record);
    }
    output
});

static PING_DATA: LazyLock<HashMap<(usize, usize), f64>> = LazyLock::new(|| {
    let mut output = HashMap::new();
    let mut counts = HashMap::new();
    let file = File::open("data/pings-2020-07-19-2020-07-20.csv").unwrap();
    let mut rdr = csv::Reader::from_reader(file);
    for result in rdr.deserialize() {
        let record: PingMeasurement = result.unwrap();
        let count = counts
            .entry((record.source, record.destination))
            .or_insert(0);
        if *count == 0 {
            output.insert((record.source, record.destination), record.avg);
        } else {
            let avg = output[&(record.source, record.destination)];
            let new_avg = (avg * *count as f64 + record.avg) / (*count + 1) as f64;
            output.insert((record.source, record.destination), new_avg);
        }
        *count += 1;
    }
    output
});

// static PING_DATA: LazyLock<Vec<PingMeasurement>> = LazyLock::new(|| {
//     let mut output = Vec::new();
//     let file = File::open("data/pings-2020-07-19-2020-07-20.csv").unwrap();
//     let mut rdr = csv::Reader::from_reader(file);
//     for result in rdr.deserialize() {
//         let record: PingMeasurement = result.unwrap();
//         output.push(record);
//     }
//     output
// });

static COUNTRY_TO_CONTINENT: LazyLock<HashMap<String, String>> = LazyLock::new(|| {
    let mut map = HashMap::new();
    let file = File::open("data/countries_iso3166.csv").unwrap();
    let mut rdr = csv::Reader::from_reader(file);
    for result in rdr.records() {
        let record = result.unwrap();
        let alpha2 = record[1].to_owned();
        let region = record[5].to_owned();
        map.insert(alpha2, region);
    }
    map
});

#[derive(Clone, Debug, serde::Deserialize)]
pub struct PingServer {
    pub id: usize,
    name: String,
    title: String,
    pub location: String,
    state: String,
    country: String,
    state_abbv: String,
    contintent: Option<u8>,
    latitude: f64,
    longitude: f64,
}

#[derive(Clone, Debug, serde::Deserialize)]
pub struct PingMeasurement {
    source: usize,
    destination: usize,
    timestamp: String,
    min: f64,
    avg: f64,
    max: f64,
    mdev: f64,
}

pub fn find_closest_ping_server(lat: f64, lon: f64) -> &'static PingServer {
    PING_SERVERS
        .iter()
        .min_by_key(|server| {
            let server_pos = Point::new(server.longitude, server.latitude);
            let target_pos = Point::new(lon, lat);
            Haversine.distance(server_pos, target_pos) as u64
        })
        .unwrap()
}

pub fn get_ping(source: usize, destination: usize) -> Option<f64> {
    PING_DATA.get(&(source, destination)).copied()
}
