# The multiple flying sidekicks traveling salesman problem with variable drone speeds (mFSTSP-VDS)

This repository provides a collection of test problems, as well as the soucre code to solve mFSTSP-VDS instances. The mFSTSP-VDS is a variant of the TSP in which multiple UAVs coordinate with a truck to deliver parcels in the minimum time, and UAVs can fly at any speeds below their maximum speeds.

The repository accompanies the following paper, which is currently under review:
> R. Raj and C. Murray. Fly slower, deliver faster: The multiple flying sidekicks traveling salesman problem with variable drone speeds. Available at SSRN: https://ssrn.com/abstract=3549622

The paper provides details on the mFSTSP-VDS definition, and a heuristic as a solution approach. 

--- 

This paper is an extension of:
> C. C. Murray and R. Raj (2020), The multiple flying sidekicks traveling salesman problem: Parcel delivery with multiple drones, Transportation Research Part C: Emerging Technologies, Volume 110, Pages 368-398.  

- The mFSTSP paper is available at:
    - https://ssrn.com/abstract=3338436 (free download from SSRN), or
    - https://www.sciencedirect.com/science/article/pii/S0968090X19302505 (published paper)

- Visit https://github.com/optimatorlab/mFSTSP for test problems, solutions, and heuristic source code for the mFSTSP.

---- 

## mFSTSP-VDS Repository Contents
This repository contains **test problems (and solutions)**, and the **source code required to run the mFSTSP-VDS solver**.  These elements are described in detail below.  

1. A collection of **test problems (and solutions)** that were used in the analysis described in the [mFSTSP-VDS paper]().

   1. [`problems_info.csv`](problems_info.csv) contains a summary of all 80 "base" test problems, including: 
      - `numCust`: Total number of customers. 
      - `LeftLon`, `LowerLat`, `RightLon`, `UpperLat`: Latitude/Longitude coordinates of the bounding region from which customer locations were generated.  These coordinates specify the SW and NE corners of a rectangle.
      - `widthOfRegion` and `heightOfRegion`: Sizes of the geographic region, available in both miles and meters.
      - `numCust5milesDepot`: Number of customers located within 5 miles (Euclidean distance) of the depot.
      - `numCust10milesDepot`: Number of customers located within 10 miles (Euclidean distance) of the depot.
   
      This file may be useful if you are looking for problems with certain properties (e.g., 50-customer problems). 
   
   2. [`performance_summary.csv`](performance_summary.csv) provides information about solutions generated for each test problem in the [mFSTSP-VDS paper](). See the ["Archived Problem Solutions"](#Archived-Problem-Solutions) section below for details on the contents of this file.
       
   3. The [`Problems`](Problems) directory contains 80 sub-directories (one for each "base" problem).  Each sub-directory contains the following groups of files:
      - There are 2 files that are required by the solver.  These 2 files must be present in order to run the solver, as they are **inputs** to the heuristic:
         - `tbl_locations.csv` describes all nodes in the problem.  `nodeType 0` represents the depot, `nodeType 1` represents a customer.  The depot is always always assigned to `nodeID 0`.  Each node has a corresponding latitude and longitude (specified in degrees).  The altitude is always 0.  Customer nodes have a corresponding non-zero parcel weight (in [pounds]).  There is no parcel associated with the depot. 
         - `tbl_truck_travel_data_PG.csv` contains the directed truck travel time and distance information from one node to another.  All time and distance values were obtained by pgRouting, using OpenStreetMaps data.
      - There is one file that was created by our "problem generator":
         - `map.html` is a webpage showing the locations of all nodes (one depot and multiple customers) associated with this problem.  This is for informational purposes only; it is neither an input to, nor an output from, the solvers.
      - Finally, there are multiple files that were generated by the solvers when we were preparing the [mFSTSP-VDS paper](). These are **outputs** from the solver (and are, therefore, not required *before* solving a problem).  
         - Numerous files of the form `tbl_solutions_<UAVtype>_<# of UAVs>_<UAVspeedType>.csv`, where 
            - `<UAVtype>` indicates the speed and range of the UAVs.  This will be `101`, `102`, `103`, or `104`.  See below for more information.
            - `<# of UAVs>` indicates the number of available UAVs.  The [mFSTSP-VDS paper]() considered 1-4 UAVs.
            - `<UAVspeedType>` will be either `fixed` (if UAV speeds were fixed, as in mFSTSP) or `variable` (if UAV speeds were variable, as in mFSTSP-VDS).
            
            Each of these files contains details about solutions corresponding to a specified combination of `<UAVtype>`, `<# of UAVs>`, and `<UAVspeedType>`.
         
   4. The `Problems` directory also contains four CSV files, of the form `tbl_vehicles_<ID>.csv` that provide information on UAV specifications, where:
      - ID [`101`](Problems/tbl_vehicles_101.csv): Maximum UAV speed is 10 m/s;
      - ID [`102`](Problems/tbl_vehicles_102.csv): Maximum UAV speed is 20 m/s;
      - ID [`103`](Problems/tbl_vehicles_103.csv): Maximum UAV speed is 30 m/s; and
      - ID [`104`](Problems/tbl_vehicles_104.csv): Maximum UAV speed is 40 m/s.

2. A folder containing **source code** for the heuristic described in the [mFSTSP-VDS paper]().

----

## Archived Problem Solutions

This repository contains solutions to the problem instances, as discussed in the analysis section of the [mFSTSP-VDS paper](). 

[`performance_summary.csv`](performance_summary.csv) provides summary information about these solutions. 
This file contains the following columns:
- `problemName` - The name of the problem instance (written in the form of a timestamp).  This is a subdirectory name within the [`Problems`](Problems) directory.
- `vehicleFileID` - Indicates the maximum speed of the UAVs (or the `tbl_vehicles_<ID>.csv` file that was used)
- `numUAVs` - # of UAVs available (`1`, `2`, `3`, or `4`).
- `UAVSpeed` - Indicates whether the problem was solved using `fixed` or `variable` UAV speeds.
- `numTrucks` - This can be ignored; it will always have a value of `-1`.  However, in each problem there is actually exactly 1 truck.
- `numCustomers` - The total number of customers.
- `timestamp` - The time at which the problem was solved.
- `ofv` - The objective function value, as obtained by the given solution approach.
- `totalTime` - The total runtime of the heuristic.
- `numUAVcust` - The number of customers assigned to the UAV(s).
- `numTruckCust` - The number of customers assigned to the truck.
- `waitingTruck` - The amount of time, in [seconds], that the truck spends waiting on UAVs.
- `waitingUAV` - The amount of time, in [seconds], that the UAVs spend waiting on the truck.

[`performance_summary.csv`](performance_summary.csv) contains records for the following classes of problems:
Each problem (there are 80 total) was run using four different settings of `vehicleFileID` (101, 102, 103, and 104) and four different settings of `numUAVs` (1, 2, 3, and 4).  Each problem was solved using both the fixed (mFSTSP) and the variable (mFSTSP-VDS) UAV speeds.  This resulted in a total of 2560 problem solutions (80 * 4 * 4 * 2).
    
Details of each solution may be found in the applicable `tbl_solutions_<UAVtype>_<# of UAVs>_<UAVspeedType>.csv` file contained within the `problemName` subdirectory of the [`Problems`](Problems) directory (e.g., [`Problems/20191118T161041628422`](Problems/20191118T161041628422)).

----

## Contact Info

For any queries, please send an email to r28@buffalo.edu.
