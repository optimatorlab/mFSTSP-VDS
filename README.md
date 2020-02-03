# The multiple flying sidekicks traveling salesman problem with variable drone speeds (mFSTSP-VDS)
This repository provides test problems, soucre codes, and heuristic pseudo-code for solving the Multiple Flying Sidekicks Traveling Salesman Problem with Variable Drone Speeds (mFSTSP-VDS). The mFSTSP-VDS is a variant of the TSP in which multiple UAVs coordinate with a truck to deliver parcels in the minimum time, and UAVs can fly at any speeds below their maximum speeds. The heuristic pseudo-code provided here in the README file is a detailed version of the one discussed in the corresponding paper:
> R. Raj and C. Murray. Fly slower, deliver faster: The multiple flying sidekicks traveling salesman problem with variable drone speeds. Available at SSRN: _____________________________________________________

## mFSTSP-VDS Heuristic:
The pseudo-code for the three-phased mFSTSP-VDS heuristic is provided below. It uses a function called **CalcUAVParams** to calculate input parameters for UAVs, the description of which is provided in Section 4.1 of the paper. For understanding of any parameters or notations in the psuedo-codes, readers are encouraged to refer to the paper. The details of the entire hueristic is provided in Section 4.
![alt text](https://github.com/optimatorlab/mFSTSP-VDS/blob/murray/Heuristic.png)

## Phase 1:
Following is the pseudo-code for Phase 1 of the heuristic, the details of which is provided in Section 4.2 of the paper. It uses a function **getTSP** which solves an MIP using lazy constraints to generate the TSP tour, the details of which is provided in Gurobi Optimization, 2017. Phase 1 uses another function called **checkFeasibility**, which solves an integer program, the description of which is provided in Section 4.2 of the paper.
![alt text](https://github.com/optimatorlab/mFSTSP-VDS/blob/murray/Phase1.png)

## Phase 2:
The pseudo-code for Phase 2 of the heuristic, which is detailed in Section 4.3 of the paper, is provided below.
![alt text](https://github.com/optimatorlab/mFSTSP-VDS/blob/murray/Phase2.png)

## Phase 3:
Following is the pseudo-code for Phase 3 of the heuristic, which is detailed in Section 4.4 of the paper. A function called **ModifySpeeds** is used within this phase, the pseudo-code for which is also provided here in the README file.
![alt text](https://github.com/optimatorlab/mFSTSP-VDS/blob/murray/Phase3.png)

![alt text](https://github.com/optimatorlab/mFSTSP-VDS/blob/murray/ModifySpeeds.png)

## Local Search:
The pseudo-code corresponding to local search part of the heuristic is provided below, the details of which can be found in Section 4.5 of the paper.
![alt text](https://github.com/optimatorlab/mFSTSP-VDS/blob/murray/LocalSearch.png)

----

## Contact Info

For any queries, please send an email to r28@buffalo.edu.
