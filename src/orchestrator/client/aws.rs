// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;

pub struct AwsClient {
    // settings: Settings,
    clients: HashMap<String, aws_sdk_ec2::Client>,
}
