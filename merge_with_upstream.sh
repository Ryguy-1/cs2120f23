#!/bin/bash

# Ensure Upstream Exists
git remote add upstream https://github.com/kevinsullivan/cs2120f23

# Fetch upstream changes
git fetch upstream

# Merge upstream changes into your branch
git merge upstream/main

