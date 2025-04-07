#!/bin/bash

cd data
if [ ! -f ./pings-2020-07-19-2020-07-20.csv ]; then
	echo "Downloading ping dataset..."
	wget https://wp-public.s3.amazonaws.com/pings/pings-2020-07-19-2020-07-20.csv.gz
	gzip -d pings-2020-07-19-2020-07-20.csv.gz
else
    echo "data/pings-2020-07-19-2020-07-20.csv already exists"
fi
