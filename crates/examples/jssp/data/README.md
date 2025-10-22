# JSSP Instance in Taillard Form

This repository contains Job Shop Scheduling Problem (JSSP) instances described in Taillard format. The format includes the number of jobs and machines, followed by a detailed representation of the operations for each job. These instances are created from anonymised real-world data.

## Format Details

1. **Header**: The first line contains two integers:
    - `N`: The number of jobs.
    - `M`: The number of machines.

    Example: 792 48

2. **Job Descriptions**: Each subsequent line represents the operations of a job, as follows:
    - Each job line begins with the operations of the job in sequential order.
    - Each operation consists of a machine index `m` and its corresponding processing time `p`.
    - Jobs may have operations that revisit the same machine (recirculation).
  
    Example: 41 646 21 75 11 133 10 140 46 770 46 748 41 794
    - The first operation is on Machine `41` and has a processing time of `646`.
    - The second operation is on Machine `21` and has a processing time of `75`.
    - ...
    - The job has recirculation, as Machine `46` appears multiple times with different processing times.

## Features

  **Recirculation Support**: The format allows jobs to have multiple operations on the same machine.
  **Flexible Number of Operations**: Jobs may have a variable number of operations. The instances do not have a rectangular shape.
