#!/usr/bin/env python

import sys
import time
import datetime
import math
from parseCSV import *
from gurobipy import *
from collections import defaultdict
import copy

import os

from mfstsp_heuristic_1_partition import *
from mfstsp_heuristic_2_asgn_uavs import *
from mfstsp_heuristic_3_timing import *

from local_search import *

import endurance_calculator
import distance_functions

import random

# 
NODE_TYPE_DEPOT	= 0
NODE_TYPE_CUST	= 1

TYPE_TRUCK 		= 1
TYPE_UAV 		= 2
#

METERS_PER_MILE = 1609.34

# http://stackoverflow.com/questions/635483/what-is-the-best-way-to-implement-nested-dictionaries-in-python
def make_dict():
	return defaultdict(make_dict)

	# Usage:
	# tau = defaultdict(make_dict)
	# v = 17
	# i = 3
	# j = 12
	# tau[v][i][j] = 44

class make_node:
	def __init__(self, nodeType, latDeg, lonDeg, altMeters, parcelWtLbs, serviceTimeTruck, serviceTimeUAV, address): 
		# Set node[nodeID]
		self.nodeType 			= nodeType
		self.latDeg 			= latDeg
		self.lonDeg				= lonDeg
		self.altMeters			= altMeters
		self.parcelWtLbs 		= parcelWtLbs
		self.serviceTimeTruck	= serviceTimeTruck	# [seconds]
		self.serviceTimeUAV 	= serviceTimeUAV	# [seconds]
		self.address 			= address			# Might be None...need MapQuest to give us this info later.

class make_assignments:
	def __init__(self, vehicleType, startTime, startNodeID, startLatDeg, startLonDeg, startAltMeters, endTime, endNodeID, endLatDeg, endLonDeg, endAltMeters, icon, description, UAVsOnBoard, ganttStatus):
		# Set assignments[v][statusID][statusIndex]
		self.vehicleType 	= vehicleType
		self.startTime 		= startTime
		self.startNodeID	= startNodeID
		self.startLatDeg 	= startLatDeg
		self.startLonDeg 	= startLonDeg
		self.startAltMeters = startAltMeters
		self.endTime 		= endTime
		self.endNodeID 		= endNodeID
		self.endLatDeg		= endLatDeg
		self.endLonDeg		= endLonDeg
		self.endAltMeters 	= endAltMeters
		self.icon			= icon
		self.description 	= description
		self.UAVsOnBoard 	= UAVsOnBoard
		self.ganttStatus	= ganttStatus

class make_packages:
	def __init__(self, packageType, latDeg, lonDeg, deliveryTime, icon):
		# Set packages[nodeID]
		self.packageType 	= packageType
		self.latDeg 		= latDeg
		self.lonDeg 		= lonDeg
		self.deliveryTime 	= deliveryTime
		self.icon 			= icon


# Function to generate TSP assignments for a given TSP tour:
def generateTSPinfo(myTour, c, C, node, tau, sigma):
	tmpAssignments = defaultdict(make_dict)

	vehicleType = TYPE_TRUCK
	UAVsOnBoard = []				
	startAltMeters = 0.0
	endAltMeters = 0.0

	i = 0					# Start at the depot
	mayEnd = 0
	tmpDepart = 0.0
	icon = 'ub_truck_1.gltf'
	for myIndex in range(1,len(myTour)):
		j = myTour[myIndex]
		# We are traveling from i to j
		# Capture the "traveling" component:
		statusID 	= TRAVEL_TRUCK_EMPTY
		ganttStatus	= GANTT_TRAVEL
		startTime 	= tmpDepart	# When we departed from i
		startNodeID = i
		startLatDeg = node[i].latDeg
		startLonDeg	= node[i].lonDeg
		endTime		= startTime + tau[i][j]	# This is when we arrive at j
		endNodeID	= j
		endLatDeg	= node[j].latDeg
		endLonDeg	= node[j].lonDeg
		if ((i in C) and (j in C)):	
			description 	= 'Driving from Customer %d to Customer %d' % (i,j)						
		elif ((i == 0) and (j in C)):
			description 	= 'Driving from Depot to Customer %d' % (j)
		elif ((i in C) and (j == c+1)):
			description 	= 'Returning to the Depot from Customer %d' % (i)
		elif ((i == 0) and (j == c+1)):
			description 	= 'Truck 1 was not used' 
		else:
			print('WE HAVE A PROBLEM.  What is the proper description?')
			print('\t Quitting Now.')
			exit()

		if (0 in tmpAssignments[1][statusID]):
			statusIndex = len(tmpAssignments[1][statusID])
		else:
			statusIndex = 0
		
		tmpAssignments[1][statusID][statusIndex] = make_assignments(vehicleType, startTime, startNodeID, startLatDeg, startLonDeg, startAltMeters, endTime, endNodeID, endLatDeg, endLonDeg, endAltMeters, icon, description, UAVsOnBoard, ganttStatus)


		# Now, capture the "service" component:
		startTime 		= endTime		# When we arrived at j
		startNodeID 	= j
		startLatDeg 	= node[j].latDeg
		startLonDeg		= node[j].lonDeg
		endTime			= startTime + sigma[j]	# This is when we finish up at j
		endNodeID		= j
		endLatDeg		= node[j].latDeg
		endLonDeg		= node[j].lonDeg
		objVal 			= endTime
		if (j == c+1):
			statusID		= STATIONARY_TRUCK_EMPTY
			ganttStatus		= GANTT_FINISHED
			description		= 'Arrived at the Depot.'
		else:
			statusID		= STATIONARY_TRUCK_EMPTY
			ganttStatus		= GANTT_DELIVER
			description		= 'Dropping off package to Customer %d' % (j)

		if (0 in tmpAssignments[1][statusID]):
			statusIndex = len(tmpAssignments[1][statusID])
		else:
			statusIndex = 0
		
		tmpAssignments[1][statusID][statusIndex] = make_assignments(vehicleType, startTime, startNodeID, startLatDeg, startLonDeg, startAltMeters, endTime, endNodeID, endLatDeg, endLonDeg, endAltMeters, icon, description, UAVsOnBoard, ganttStatus)

		tmpDepart = endTime
		if (j != c+1):
			# Go to the next arc
			i = j

	return (objVal, tmpAssignments, myTour)	
	
	
# Function to insert a UAV customer myj between two truck customers myi and myk, and obtain TSP assignments for the resulting TSP tour:		
def insertTruckCustomer(myj, myi, myk, c, C, node, tau, sigma, x):
	tmpAssignments = defaultdict(make_dict)
	
	vehicleType = TYPE_TRUCK
	UAVsOnBoard = []
	startAltMeters = 0.0
	endAltMeters = 0.0
	tmpDepart = 0.0
	icon = 'ub_truck_1.gltf'

	tmpDepart = 0.0
	
	vehicleID = 1	# Truck
	
	TSPobjVal = 0.0
	
	tmpTSPtour = []
		
	for [i1, j1] in x:
		if ((i1 == myi) and (j1 == myk)):
			# Insert myj between myi and myk:

			subtour = [[myi, myj], [myj, myk]]
		else:
			# Travel from i1 to j1
			
			subtour = [[i1, j1]]	
		
		for [i,j] in subtour:
			
			tmpTSPtour.append(i)

			# We are traveling from i to j
			# Capture the "traveling" component:
			statusID 	= TRAVEL_TRUCK_EMPTY
			ganttStatus	= GANTT_TRAVEL
			startTime 	= tmpDepart		# When we departed from i
			startNodeID = i
			startLatDeg = node[i].latDeg
			startLonDeg	= node[i].lonDeg
			endTime		= startTime + tau[i][j]	# This is when we arrive at j
			endNodeID	= j
			endLatDeg	= node[j].latDeg
			endLonDeg	= node[j].lonDeg
			if ((i in C) and (j in C)):
				description 	= 'Driving from Customer %d to Customer %d' % (i,j)
			elif ((i == 0) and (j in C)):
				description 	= 'Driving from Depot to Customer %d' % (j)
			elif ((i in C) and (j == c+1)):
				description 	= 'Returning to the Depot from Customer %d' % (i)
			elif ((i == 0) and (j == c+1)):
				description 	= 'Truck 1 was not used'
			else:
				print('WE HAVE A PROBLEM.  What is the proper description?')
				print('\t Quitting Now.')
				exit()

			if (0 in tmpAssignments[1][statusID]):
				myIndex = len(tmpAssignments[1][statusID])
			else:
				myIndex = 0

			TSPobjVal = max(TSPobjVal, endTime)
			
			tmpAssignments[1][statusID][myIndex] = make_assignments(vehicleType, startTime, startNodeID, startLatDeg, startLonDeg, startAltMeters, endTime, endNodeID, endLatDeg, endLonDeg, endAltMeters, icon, description, UAVsOnBoard, ganttStatus)
		

			# Now, capture the "service" component at myj:
			startTime 		= endTime		# When we arrived at j
			startNodeID 	= j
			startLatDeg 	= node[j].latDeg
			startLonDeg		= node[j].lonDeg
			endTime			= startTime + sigma[j]	# This is when we finish up at j
			endNodeID		= j
			endLatDeg		= node[j].latDeg
			endLonDeg		= node[j].lonDeg

			statusID		= STATIONARY_TRUCK_EMPTY
			ganttStatus		= GANTT_DELIVER
			description		= 'Dropping off package to Customer %d' % (j)
			
			if (0 in tmpAssignments[1][statusID]):
				myIndex = len(tmpAssignments[1][statusID])
			else:
				myIndex = 0

			TSPobjVal = max(TSPobjVal, endTime)

			tmpAssignments[1][statusID][myIndex] = make_assignments(vehicleType, startTime, startNodeID, startLatDeg, startLonDeg, startAltMeters, endTime, endNodeID, endLatDeg, endLonDeg, endAltMeters, icon, description, UAVsOnBoard, ganttStatus)
	
			tmpDepart = endTime
	
	tmpTSPtour.append(c+1)
	
	return (tmpAssignments, TSPobjVal, tmpTSPtour)

		
def solve_mfstsp_heuristic(node, vehicle, travel, problemName, vehicleFileID, numUAVs, UAVSpeedType):
	
	# Establish system parameters:
	C 			= [] # List of customers
	tau			= defaultdict(make_dict) # Truck travel time
	xtauprimeF	= defaultdict(make_dict) # Initial UAV travel time with a package
	xtauprimeE	= defaultdict(make_dict) # Initial UAV travel time without a package
	xspeedF		= defaultdict(make_dict) # Initial UAV speed with a package
	xspeedE 		= defaultdict(make_dict) # Initial UAV speed without a package
	xeee 		= defaultdict(make_dict) # Initial endurance (in seconds) of vehicle v if it travels from i --> j --> k
	xeeePrime 	= defaultdict(make_dict) # Maximum possible Enduance (in seconds) of vehicle v if it is launched from i and retrieved at k
	V			= []		# Set of UAVs.
	sL			= defaultdict(make_dict) # Launch service time of UAVs
	sR			= defaultdict(make_dict) # Retrieval service time of UAVs
	sigma		= {} # Time to deliver a customer by truck
	sigmaprime	= {} # Time to deliver a customer by UAV

	for nodeID in node:	
		if (node[nodeID].nodeType == NODE_TYPE_CUST):
			C.append(nodeID)		# C is the vector of customer nodes.  C = [1, 2, ..., c]
			
			
	for vehicleID in vehicle:
		if (vehicle[vehicleID].vehicleType == TYPE_UAV):
			V.append(vehicleID) 	
												
	c = len(C)				# c is the number of customers
	N = range(0,c+2)		# N = [0, 1, 2, ..., c+1]
	N_zero = range(0,c+1)	# N_zero = [0, 1, ..., c]
	N_plus = range(1,c+2)	# N_plus = [1, 2, ..., c+1]
	
	
	# We need to define node c+1, which is a copy of the depot.
	node[c+1] = make_node(node[0].nodeType, node[0].latDeg, node[0].lonDeg, node[0].altMeters, node[0].parcelWtLbs, node[0].serviceTimeTruck, node[0].serviceTimeUAV, node[0].address) 
	

	initializedSpeeds = {}
	# Choose the initial speeds for different parcel weights (in lbs) based on the UAVSpeedType for which the problem is being solved:
	if UAVSpeedType == 1:
		initializedSpeeds[1] = {-1:13.96 + 10.0, 0: 13.96 + 10.0, 1: 15.93 + 10.0, 2: 17.68 + 10.0, 3: 19.28 + 10.0, 4: 20.75 + 10.0, 5: 22.12 + 10.0}
		initializedSpeeds[2] = {-1:13.96, 0: 13.96, 1: 15.93, 2: 17.68, 3: 19.28, 4: 20.75, 5: 22.12}
	elif UAVSpeedType == 2:
		initializedSpeeds[1] = {-1: vehicle[2].cruiseSpeed, 0: vehicle[2].cruiseSpeed, 1: vehicle[2].cruiseSpeed, 2: vehicle[2].cruiseSpeed, 3: vehicle[2].cruiseSpeed, 4: vehicle[2].cruiseSpeed, 5: vehicle[2].cruiseSpeed}
		initializedSpeeds[2] = {-1: vehicle[2].cruiseSpeed, 0: vehicle[2].cruiseSpeed, 1: vehicle[2].cruiseSpeed, 2: vehicle[2].cruiseSpeed, 3: vehicle[2].cruiseSpeed, 4: vehicle[2].cruiseSpeed, 5: vehicle[2].cruiseSpeed}
	elif UAVSpeedType == 3:
		initializedSpeeds[1] = {-1:13.96, 0: 13.96, 1: 15.93, 2: 17.68, 3: 19.28, 4: 20.75, 5: 22.12}
		initializedSpeeds[2] = {-1:13.96, 0: 13.96, 1: 15.93, 2: 17.68, 3: 19.28, 4: 20.75, 5: 22.12}
	else:
		print("ERROR: Choose a valid UAVSpeedType")
		exit()


	# Build tau (truck) and tauprime (UAV):
	minDistance = 0			# We'll use this to calculate big M later
	for vehicleID in vehicle:
		for i in N_zero:
			for j in N_zero:
				for sr in initializedSpeeds:
					xeeePrime[sr][vehicleID][i][j] = 0

				if (vehicle[vehicleID].vehicleType == TYPE_TRUCK):
					tau[i][j] = travel[vehicleID][i][j].totalTime
					if (tau[i][j] > minDistance):
						minDistance = tau[i][j]
				elif (vehicle[vehicleID].vehicleType == TYPE_UAV):
					for sr in initializedSpeeds:
						xspeedE[sr][vehicleID][i][j] = min(initializedSpeeds[sr][0], vehicle[vehicleID].cruiseSpeed)
						[takeoffTime, flyTime, landTime, totalTimeEnd, takeoffDistance, flyDistance, landDistance, totalDistance] = distance_functions.calcMultirotorTravelTime(vehicle[vehicleID].takeoffSpeed, xspeedE[sr][vehicleID][i][j], vehicle[vehicleID].landingSpeed, vehicle[vehicleID].yawRateDeg, node[i].altMeters, vehicle[vehicleID].cruiseAlt, node[j].altMeters, node[i].latDeg, node[i].lonDeg, node[j].latDeg, node[j].lonDeg, -361, -361)
						xtauprimeE[sr][vehicleID][i][j] = totalTimeEnd
						if node[j].parcelWtLbs > 5:
							xspeedF[sr][vehicleID][i][j] = vehicle[vehicleID].cruiseSpeed
							xtauprimeF[sr][vehicleID][i][j] = travel[vehicleID][i][j].totalTime
						else:
							xspeedF[sr][vehicleID][i][j] = min(initializedSpeeds[sr][node[j].parcelWtLbs], vehicle[vehicleID].cruiseSpeed)
							[takeoffTime, flyTime, landTime, totalTimeEnd, takeoffDistance, flyDistance, landDistance, totalDistance] = distance_functions.calcMultirotorTravelTime(vehicle[vehicleID].takeoffSpeed, xspeedF[sr][vehicleID][i][j], vehicle[vehicleID].landingSpeed, vehicle[vehicleID].yawRateDeg, node[i].altMeters, vehicle[vehicleID].cruiseAlt, node[j].altMeters, node[i].latDeg, node[i].lonDeg, node[j].latDeg, node[j].lonDeg, -361, -361)
							xtauprimeF[sr][vehicleID][i][j] = totalTimeEnd
				else:
					print("ERROR:  Vehicle Type %d is not defined." % (vehicle[vehicleID].vehicleType))
					quit()	
					
			# NOTE: We need to capture the travel time to node c+1 (which is the same physical location as node 0):
			for sr in initializedSpeeds:
				xeeePrime[sr][vehicleID][i][c+1] = 0
			
			if (vehicle[vehicleID].vehicleType == TYPE_TRUCK):
				tau[i][c+1] = travel[vehicleID][i][0].totalTime
				if (tau[i][c+1] > minDistance):
					minDistance = tau[i][c+1]
			elif (vehicle[vehicleID].vehicleType == TYPE_UAV):
				for sr in initializedSpeeds:
					xspeedE[sr][vehicleID][i][c+1] = min(initializedSpeeds[sr][0], vehicle[vehicleID].cruiseSpeed)
					xspeedF[sr][vehicleID][i][c+1] = min(initializedSpeeds[sr][0], vehicle[vehicleID].cruiseSpeed)
					[takeoffTime, flyTime, landTime, totalTimeEnd, takeoffDistance, flyDistance, landDistance, totalDistance] = distance_functions.calcMultirotorTravelTime(vehicle[vehicleID].takeoffSpeed, xspeedE[sr][vehicleID][i][c+1], vehicle[vehicleID].landingSpeed, vehicle[vehicleID].yawRateDeg, node[i].altMeters, vehicle[vehicleID].cruiseAlt, node[0].altMeters, node[i].latDeg, node[i].lonDeg, node[0].latDeg, node[0].lonDeg, -361, -361)				
					xtauprimeE[sr][vehicleID][i][c+1] = totalTimeEnd
					xtauprimeF[sr][vehicleID][i][c+1] = totalTimeEnd
			else:
				print("ERROR:  Vehicle Type %d is not defined." % (vehicle[vehicleID].vehicleType))
				quit()	
										
										
	# Build the set of all possible sorties: [v, i, j, k]
	xP = {}
	for sr in initializedSpeeds:
		xP[sr] = []

	for v in V:		# vehicle
		for i in N_zero:
			for j in C:
				if ((j != i) and (node[j].parcelWtLbs <= vehicle[v].capacityLbs)):
					for k in N_plus:
						if (k != i) and (k != j):

							for sr in initializedSpeeds:
								# Calculate the endurance for each sortie:
								if (k == c+1):
									xeee[sr][v][i][j][k] = endurance_calculator.give_endurance(node, vehicle, travel, v, i, j, 0, xtauprimeF[sr][v][i][j], xtauprimeE[sr][v][j][c+1], xspeedF[sr][v][i][j], xspeedE[sr][v][j][c+1])
								else:	
									xeee[sr][v][i][j][k] = endurance_calculator.give_endurance(node, vehicle, travel, v, i, j, k, xtauprimeF[sr][v][i][j], xtauprimeE[sr][v][j][k], xspeedF[sr][v][i][j], xspeedE[sr][v][j][k])
								xeeePrime[sr][v][i][k] = max(xeeePrime[sr][v][i][k], xeee[sr][v][i][j][k])		# This is only used in Phase 2

								if (xtauprimeF[sr][v][i][j] + node[j].serviceTimeUAV + xtauprimeE[sr][v][j][k] <= xeee[sr][v][i][j][k]):
									if (tau[i][k] <= xeee[sr][v][i][j][k]):
										xP[sr].append([v,i,j,k])									


	# Build the launch service times:
	for v in V:
		for i in N_zero:
			sL[v][i] = vehicle[v].launchTime
			
	# Build the recovery service times:
	for v in V:
		for k in N_plus:
			sR[v][k] = vehicle[v].recoveryTime

	# Build the customer service times:
	sigma[0] = 0.0
	for k in N_plus:
		if (k == c+1):
			sigma[k] = 0.0
			sigmaprime[k] = 0.0
		else:
			sigma[k] = node[k].serviceTimeTruck	
			sigmaprime[k] = node[k].serviceTimeUAV
		

	# Initialize the variable that keeps track of best objective found so far:
	bestOFV = float('inf')

	
	# Calculate the lower truck limit
	LTLbase = int(math.ceil((float(len(C) - len(V))/float(1 + len(V)))))

	
	prevTSPtours = []	# List to store all the TSPs that we will see in this problem instance


	p1_previousTSP = {}
	for sr in initializedSpeeds:
		p1_previousTSP[sr] = []

	FEASobjVal = 0

	iterStop = 0

	# Main loop of the mFSTSP-VDS heuristic starts here (Algorithm 1):
	for LTL in range(LTLbase, c+1):

		if iterStop >= 10: # If no better solution found in 10 iterations, then stop.
			break
	
		requireUniqueTSP = True

		Queue = []

		for sr in initializedSpeeds:
			# Partition customers between truck and UAVs, and generate a unique truck tour:
			[FEASobjVal, customersTruck, customersUAV, TSPobjVal, TSPassignments, TSPpackages, TSPtour, foundTSP, prevTSPtours, p1_previousTSP[sr]] = mfstsp_heuristic_1_partition(node, vehicle, travel, N, N_zero, N_plus, C, xP[sr], tau, xtauprimeE[sr], xtauprimeF[sr], sigma, sigmaprime, sL, sR, LTL, requireUniqueTSP, prevTSPtours, bestOFV, p1_previousTSP[sr], FEASobjVal)	

			# If we cant find a unique TSP tour, go back to the start of Phase I with a new LTL:
			if (not foundTSP):
				continue

			# Generate a lower bound:
			optLowBnd = TSPobjVal
			for j in customersUAV:
				v = 2
				optLowBnd += sL[v][j]
				optLowBnd += sR[v][j]
			
			# If lower bound is greater than the current OFV, go back to the start of Phase I with a new LTL:	
			if (optLowBnd >= bestOFV):
				iterStop += 1
				continue
			else:
				iterStop = 0

			# Add the new TSP to the list of candidate TSP solutions:
			Queue.append(list([TSPassignments, customersUAV, customersTruck, TSPobjVal]))

		while len(Queue) != 0:

			[TSPassignments, customersUAV, customersTruck, TSPobjVal] = Queue.pop(0)

			for sr in initializedSpeeds:
				# Create UAV sorties <v,i,j,k> (a pair of launch-recovery points and a UAV for each UAV customer)
				[multiInsertCost, x, multiY, multiZ, multiInsertTuple] = mfstsp_heuristic_2_asgn_uavs(node, xeee[sr], xeeePrime[sr], N_zero, N_plus, C, V, c, TSPassignments, customersUAV, customersTruck, sigma, sigmaprime, tau, xtauprimeE[sr], xtauprimeF[sr], vehicle, sL, sR, prevTSPtours)

				# For each candidate Phase 2 solution, solve Phase 3:
				for yind in range(0,len(multiY)):
					insertCost = multiInsertCost[yind]
					y = list(multiY[yind])
					z = list(multiZ[yind])
					insertTuple = dict(multiInsertTuple[yind])

					# Generate an optimistic lower bound assuming that truck never waits for UAVs:
					optLowBnd = TSPobjVal
					optLowBnd += insertCost
					for [v,i,j,k] in y:
						if (i != 0):
							optLowBnd += sL[v][i]
						optLowBnd += sR[v][k]

					# Check for lower bound:
					if (optLowBnd > bestOFV):	# lower bound is greater than the current OFV, so go back to the next Phase 2 candidate solution
						canDo3 = False
						continue

					else:	# lower bound is promising, check for Phase II feasibility
						if (len(z) > 0):	# Phase II is not feasible, bceause customer z does not have a feasible assignment
							canDo3 = False

							# Let's try inserting a UAV customer with infeasible assignment in truck route:

							# The UAV customer with cheapest insertion cost is z[0], and corresponding insertion location information is stored in insertTuple.
							# Use insertTuple to create a new TSP, and obtain corresponding TSP assignments as following:

							[tmpTSPassignments, tmpTSPobjVal, tmpTSPtour] = insertTruckCustomer(insertTuple['j'], insertTuple['i'], insertTuple['k'], c, C, node, tau, sigma, x)

							if (tmpTSPtour not in prevTSPtours):
								# Add the new TSP tour to the list of candidate TSP solutions:
								tmpCustomersTruck = list(customersTruck)
								tmpCustomersUAV = list(customersUAV)
								tmpCustomersTruck.append(z[0])
								tmpCustomersUAV.remove(z[0])

								Queue.append(list([tmpTSPassignments, tmpCustomersUAV, tmpCustomersTruck, tmpTSPobjVal]))
								prevTSPtours.append(tmpTSPtour)

						else:	# Phase II is feasible, and it seems worthwhile to try Phase III
							canDo3 = True				


					if (canDo3):
						for P3Type in [1,2,3]:
						
							# Solve Phase 3 to determine the schedule of different activities:
							[p3isFeasible, p3objVal, tmpAssignmentsArray, tmpPackagesArray, waitingTruck, waitingUAV, waitingArray, landsat, launchesfrom, ls_checkt, ls_hatt, ls_checktprime, newTauprimeE, newTauprimeF, newSpeedE, newSpeedF, neweee] = mfstsp_heuristic_3_timing(x, y, z, node, xeee[sr], N, xP[sr], V, c, sigma, sigmaprime, tau, xtauprimeE[sr], xtauprimeF[sr], minDistance, sR, sL, vehicle, travel, optLowBnd, xspeedE[sr], xspeedF[sr], P3Type, UAVSpeedType)


							# Check Phase 3 feasibility:
							if (p3isFeasible):												
								
								# Update the incumbent:
								if (p3objVal < bestOFV):
									
									assignmentsArray = tmpAssignmentsArray
									packagesArray = tmpPackagesArray
									objVal = p3objVal

									bestWaitingTruck = waitingTruck
									bestWaitingUAV = waitingUAV
									
									bestOFV = p3objVal

								tempOFV = float('inf')

								# Re-solve Phase 3 based on modified speeds, until infeasible or no better solution found:
								while (True):
									[p3isFeasible, p3objVal, tmpAssignmentsArray, tmpPackagesArray, waitingTruck, waitingUAV, discardWaitingArray, landsat, launchesfrom, discardls_checkt, discardls_hatt, discardls_checktprime, newTauprimeE, newTauprimeF, newSpeedE, newSpeedF, neweee] = mfstsp_heuristic_3_timing(x, y, z, node, neweee, N, xP[sr], V, c, sigma, sigmaprime, tau, newTauprimeE, newTauprimeF, minDistance, sR, sL, vehicle, travel, optLowBnd, newSpeedE, newSpeedF, P3Type, UAVSpeedType)
								
									if (p3isFeasible):	

										if (p3objVal < bestOFV):
											
											assignmentsArray = tmpAssignmentsArray
											packagesArray = tmpPackagesArray
											objVal = p3objVal

											bestWaitingTruck = waitingTruck
											bestWaitingUAV = waitingUAV
											
											bestOFV = p3objVal

										if p3objVal < tempOFV:
											tempOFV = p3objVal
										else:
											break
									else:
										break


								# Perform local search until infeasible or no shift (try shifting retrieval points for UAVs to the next location, if the truck waits at the current retrieval location)
								while (True):
									[shift_happened, tmp_y] = local_search(x, y, c, waitingArray, landsat, launchesfrom, ls_checktprime, xeee[sr], tau, xtauprimeE[sr], xtauprimeF[sr], sigma, sigmaprime, ls_checkt, ls_hatt, V, sL, sR)

									if shift_happened == True: # Shift is possible. Therefore re-solve Phase 3 after making those shifts, and obtain new solution
										[p3isFeasible, p3objVal, tmpAssignmentsArray, tmpPackagesArray, waitingTruck, waitingUAV, waitingArray, landsat, launchesfrom, ls_checkt, ls_hatt, ls_checktprime, newTauprimeE, newTauprimeF, newSpeedE, newSpeedF, neweee] = mfstsp_heuristic_3_timing(x, tmp_y, z, node, xeee[sr], N, xP[sr], V, c, sigma, sigmaprime, tau, xtauprimeE[sr], xtauprimeF[sr], minDistance, sR, sL, vehicle, travel, optLowBnd, xspeedE[sr], xspeedF[sr], P3Type, UAVSpeedType)

										# Check Phase 3 feasibility:
										if (p3isFeasible):	# Phase 3 is feasible

											y = []
											for [v,i,j,k] in tmp_y:
												y.append([v,i,j,k])												
											
											# Update the incumbent:
											if (p3objVal < bestOFV):
												
												assignmentsArray = tmpAssignmentsArray
												packagesArray = tmpPackagesArray
												objVal = p3objVal

												bestWaitingTruck = waitingTruck
												bestWaitingUAV = waitingUAV
												
												bestOFV = p3objVal


											tempOFV = float('inf')
											# Re-solve Phase 3 based on modified speeds, until infeasible or no better solution found:
											while (True):
												[p3isFeasible, p3objVal, tmpAssignmentsArray, tmpPackagesArray, waitingTruck, waitingUAV, discardWaitingArray, landsat, launchesfrom, discardls_checkt, discardls_hatt, discardls_checktprime, newTauprimeE, newTauprimeF, newSpeedE, newSpeedF, neweee] = mfstsp_heuristic_3_timing(x, y, z, node, neweee, N, xP[sr], V, c, sigma, sigmaprime, tau, newTauprimeE, newTauprimeF, minDistance, sR, sL, vehicle, travel, optLowBnd, newSpeedE, newSpeedF, P3Type, UAVSpeedType)
											
												if (p3isFeasible):

													if (p3objVal < bestOFV):
														
														assignmentsArray = tmpAssignmentsArray
														packagesArray = tmpPackagesArray
														objVal = p3objVal

														bestWaitingTruck = waitingTruck
														bestWaitingUAV = waitingUAV
														
														bestOFV = p3objVal

													if p3objVal < tempOFV:
														tempOFV = p3objVal
													else:
														break
												else:
													break

										else:	# Phase III is infeasible
											break
										
									else:	# Shift is not possible
										break
				# End Phase 2 loop
	# End LTL loop
	

	# Convert best solution to "assignments" and "packages" classes
	packages = {}
	assignments = defaultdict(make_dict)
	
	for j in packagesArray:
		packages[j] = make_packages(packagesArray[j][0], packagesArray[j][1], packagesArray[j][2], packagesArray[j][3], packagesArray[j][4])

	for v in vehicle:
		for i in range(0, len(assignmentsArray[v])):
			statusID = assignmentsArray[v][i][0]
			if (0 in assignments[v][statusID]):
				statusIndex = len(assignments[v][statusID])
			else:
				statusIndex = 0
			
			assignments[v][statusID][statusIndex] = make_assignments(assignmentsArray[v][i][1], assignmentsArray[v][i][2], assignmentsArray[v][i][3], assignmentsArray[v][i][4], assignmentsArray[v][i][5], assignmentsArray[v][i][6], assignmentsArray[v][i][7], assignmentsArray[v][i][8], assignmentsArray[v][i][9], assignmentsArray[v][i][10], assignmentsArray[v][i][11], assignmentsArray[v][i][12], assignmentsArray[v][i][13], assignmentsArray[v][i][14], assignmentsArray[v][i][15])
	
		
	return(objVal, assignments, packages, bestWaitingTruck, bestWaitingUAV)