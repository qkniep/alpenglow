// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use tokio::time::{Duration, Instant, sleep};

/// Token bucket for rate limiting.
pub struct TokenBucket {
    /// Current number of tokens in the bucket.
    bucket: usize,
    /// Maximum number of tokens the bucket can hold.
    capacity: usize,
    /// Rate at which the bucket is refilled (tokens/second).
    refill_rate: usize,
    /// Last time the bucket was refilled.
    last_refill: Instant,
}

impl TokenBucket {
    /// Creates a new token bucket with the given refill rate.
    #[must_use]
    pub fn new(refill_rate: usize) -> Self {
        Self {
            bucket: 1500,
            capacity: 1000 * 1500,
            refill_rate,
            last_refill: Instant::now(),
        }
    }

    /// Refills the bucket with the correct number of tokens,
    /// based on the time since the last refill.
    pub fn refill(&mut self) {
        let now = Instant::now();
        let elapsed = now.duration_since(self.last_refill);
        let added = (self.refill_rate as f64 * elapsed.as_nanos() as f64 / 1e9) as usize;
        self.bucket = (self.bucket + added).min(self.capacity);
        self.last_refill = now;
    }

    /// Waits until the bucket has at least `bytes` tokens.
    pub async fn wait_for(&mut self, tokens: usize) {
        loop {
            self.refill();

            if self.bucket >= tokens {
                self.bucket -= tokens;
                break;
            }

            let wait_time =
                Duration::from_secs_f64((tokens - self.bucket) as f64 / self.refill_rate as f64);
            sleep(wait_time).await;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // testing token bucket accuracy to within +/-3% margin
    const ACCURACY: f64 = 0.03;

    async fn token_bucket_experiment(bucket_rate: usize, elements: usize, element_size: usize) {
        let mut bucket = TokenBucket::new(bucket_rate);
        let now = Instant::now();

        for _ in 0..elements {
            bucket.wait_for(element_size).await;
        }

        let elapsed = now.elapsed().as_secs_f64();
        let expected = elements as f64 * element_size as f64 / bucket_rate as f64;

        assert!(elapsed > expected * (1.0 - ACCURACY));
        assert!(elapsed < expected * (1.0 + ACCURACY));
    }

    #[tokio::test]
    async fn low_rate() {
        // 256 KiB/s : 1000 packets a 1500 bytes
        token_bucket_experiment(256 * 1024, 1000, 1500).await;
    }

    #[tokio::test]
    async fn high_rate() {
        // 100 MiB/s : 500k packets a 1500 bytes
        token_bucket_experiment(100 * 1024 * 1024, 500_000, 1500).await;
    }

    // When run concurrently with other tests on github, then the test fails.
    // Running sequentially seems to help.
    #[tokio::test]
    #[ignore]
    async fn extreme_rate() {
        // 1 GiB/s : 5M packets a 1500 bytes
        token_bucket_experiment(1024 * 1024 * 1024, 5_000_000, 1500).await;
    }
}
