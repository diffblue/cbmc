#!/usr/bin/env Rscript

stopifnot(interactive())

if (!exists("bininfo_result")) {
  bininfo_result <- "bininfo_result.csv"
}

cc <- c("character", "integer", "logical", "integer", "integer", "logical", "logical", "integer", "logical")
d <- read.csv(bininfo_result, colClasses=cc, na.strings="-")

# Version with abbreviated test names for easier viewing
ds <- d
ds$test <- substr(ds$test, nchar(ds$test) - 30, nchar(ds$test))