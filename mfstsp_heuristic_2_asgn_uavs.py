#!/usr/bin/env python

import sys
import time
import datetime
import math
from parseCSV import *
from gurobipy import *
from collections import defaultdict

# =============================================================
NODE_TYPE_DEPOT		= 0
NODE_TYPE_CUST		= 1

TYPE_TRUCK 			= 1
TYPE_UAV 			= 2

TRAVEL_UAV_PACKAGE		= 1
TRAVEL_UAV_EMPTY		= 2
TRAVEL_TRUCK_W_UAV		= 3
TRAVEL_TRUCK_EMPTY		= 4

VERTICAL_UAV_EMPTY		= 5
VERTICAL_UAV_PACKAGE	= 6

STATIONARY_UAV_EMPTY	= 7
STATIONARY_UAV_PACKAGE	= 8
STATIONARY_TRUCK_W_UAV	= 9
STATIONARY_TRUCK_EMPTY	= 10

# There's a package color that corresponds to the VEHICLE that delivered the package.
# Right now we only have 5 boxes (so we can have at most 5 trucks).
packageIcons		= ['', 'box_blue_centered.gltf', 'box_orange_centered.gltf', 'box_green_centered.gltf', 'box_gray_centered.gltf', 'box_brown_centered.gltf']
# =============================================================


# http://stackoverflow.com/questions/635483/what-is-the-best-way-to-implement-nested-dictionaries-in-python
def make_dict():
	return defaultdict(make_dict)

	# Usage:
	# tau = defaultdict(make_dict)
	# v = 17
	# i = 3
	# j = 12
	# tau[v][i][j] = 44


def mfstsp_heuristic_2_asgn_uavs(node, eee, eeePrime, N_zero, N_plus, C, V, c, assignments, customersUAV, customersTruck, sigma, sigmaprime, tau, tauprimeE, tauprimeF, vehicle, sL, sR, prevTSPtours):

	#-------------------------------------ALGORITHM 6 (Find the set of feasible sorties for each UAV customer) STARTS HERE--------------------------------------#
	UAVCustSupport = defaultdict(make_dict)
		
	# Get the truck arrival times and build the ordered list of truck visits.
	t = {}	
	myX = []
	myOrderedList = []
	myOrderedList.append(0)	# Initialize with depot.
	for vehicleID in assignments:
		for statusID in assignments[vehicleID]:
			for asgnIndex in assignments[vehicleID][statusID]:
				if (assignments[vehicleID][statusID][asgnIndex].vehicleType == TYPE_TRUCK):		
					if (statusID in [TRAVEL_TRUCK_W_UAV, TRAVEL_TRUCK_EMPTY]):
						i = assignments[vehicleID][statusID][asgnIndex].startNodeID
						j = assignments[vehicleID][statusID][asgnIndex].endNodeID
						
						if (j not in customersTruck):
							# When we solve the TSP, we only use a subset of nodes.  
							# This causes the TSP solution to return a final node that's not c+1.
							j = c+1
							bigM = assignments[vehicleID][statusID][asgnIndex].endTime

						myX.append([i,j])
						if i == 0:
							t[i] = assignments[vehicleID][statusID][asgnIndex].startTime
						t[j] = assignments[vehicleID][statusID][asgnIndex].endTime
						
						if (j in C):
							myOrderedList.append(j)	
	myOrderedList.append(c+1)
	
	# Reset N_zero -- Should only include customers visted by the truck, plus depot 0.	
	# Reset N_plus -- Should only include customers visted by the truck, plus depot c+1.	
	N_zero = []
	N_plus = []
	N_zero.append(0)
	for i in customersTruck:
		N_zero.append(i)
		N_plus.append(i)
	
	N_plus.append(c+1)
	
	# Reset C -- Should only include customers NOT visited by the truck
	C = []
	for i in customersUAV:
		C.append(i)
		
	
	# Find the cost of inserting truck customers:
	insertCost = {}
	for j in C:
		insertCost[j] = float('inf')
		for [i,k] in myX:
			tmpCost = max(0, (tau[i][j] + sigma[j] + tau[j][k] - tau[i][k]))
			
			if (tmpCost < insertCost[j]):
				insertCost[j] = tmpCost	


	# Calculate the number of skips allowed in total for a given truck route and number of customers:
	totalNumSkipsAllowed = len(V)*(len(myOrderedList) - 1) - len(customersUAV)

	maxSkip = min(3 , totalNumSkipsAllowed)

	supportCount = {}
	for i in range(0,maxSkip+1):
		supportCount[i] = {}
		for j in C:
			UAVCustSupport[i][j] = []
			supportCount[i][j] = 0

	for v in V:
		for tmpi in range(0,len(myOrderedList)-1):
			i = myOrderedList[tmpi]
			tmpkUpper = min(tmpi+2+maxSkip, len(myOrderedList))		
			for tmpk in range(tmpi+1,tmpkUpper):	
				k = myOrderedList[tmpk]
				if (t[k] - t[i] - sigma[i] > eeePrime[v][i][k]):
					break	# exit out of k loop				
				for j in customersUAV:							
					if (tauprimeF[v][i][j] + node[j].serviceTimeUAV + tauprimeE[v][j][k] <= eee[v][i][j][k]) and (t[k] - t[i] - sigma[i] < eee[v][i][j][k]):					
						UAVCustSupport[tmpk-(tmpi+1)][j].append([v,i,k]) # List of potential sorties for each UAV customer


	#-------------------------------------ALGORITHM 7 (Assign a sortie to each UAV customer) STARTS HERE--------------------------------------#
	myY = {}
	bigZ = {}

	SortedCust = {}


	for i in UAVCustSupport:
		for j in C:
			for k in range(i,maxSkip+1):
				supportCount[k][j] += len(UAVCustSupport[i][j])

	# Sort UAV customers in the ascending order of number of potential sorties they have:
	for i in supportCount:
		SortedCust[i] = []
		for j in sorted(supportCount[i], key=lambda j: supportCount[i][j]):
			SortedCust[i].append(j)


	# Main loop of the sortie assignment process (in which UAV waiting is preferred) starts here:
	for tmpMaxSkip in SortedCust:

		myY[tmpMaxSkip] = []
		bigZ[tmpMaxSkip] = []

		# Calculate the number of skips allowed in total for a given truck route and number of customers:
		totalNumSkipsAllowed = len(V)*(len(myOrderedList) - 1) - len(customersUAV)

		availUAVs = {}
		for i in N_zero:
			availUAVs[i] = list(V)

		# Create UAV sorties for each UAV customer:
		for j in SortedCust[tmpMaxSkip]:

			Waiting = 10*bigM

			sortie = []

			for abc in range(0 , min(tmpMaxSkip,totalNumSkipsAllowed)+1):

				for [v,i,k] in UAVCustSupport[abc][j]:
					tempp = myOrderedList.index(i)
					tempq = myOrderedList.index(k)
					availability = True
					for tempindex in range(tempp,tempq):
						if v not in availUAVs[myOrderedList[tempindex]]:
							availability = False
							break

					if availability == True:
						tempWaiting = (tauprimeF[v][i][j] + node[j].serviceTimeUAV + tauprimeE[v][j][k]) - (t[k] - t[i])

						if tempWaiting >= 0:
							if tempWaiting < Waiting:
								Waiting = tempWaiting
								sortie = [v,i,j,k]

						else:
							if Waiting >= 0:
								Waiting = tempWaiting
								sortie = [v,i,j,k]
							else:
								if Waiting < tempWaiting:
									Waiting = tempWaiting
									sortie = [v,i,j,k]

			# If no sortie is found for customer j, append it to the list bigZ:
			if len(sortie) == 0:
				if tmpMaxSkip == 0:
					bigZ[tmpMaxSkip].append(j)
				else:
					del myY[tmpMaxSkip]
					del bigZ[tmpMaxSkip]
					break

			else:
				myY[tmpMaxSkip].append(sortie)
				tempp = myOrderedList.index(sortie[1])
				tempq = myOrderedList.index(sortie[3])

				totalNumSkipsAllowed = totalNumSkipsAllowed - (tempq-tempp-1)

				for tempindex in range(tempp,tempq):
					availUAVs[myOrderedList[tempindex]].remove(sortie[0])


	# Main loop of the sortie assignment process (in which truck waiting is preferred) starts here:
	for tmpMaxSkip in SortedCust:

		myY[tmpMaxSkip+maxSkip+1] = []
		bigZ[tmpMaxSkip+maxSkip+1] = []

		# Calculate the number of skips allowed in total for a given truck route and number of customers:
		totalNumSkipsAllowed = len(V)*(len(myOrderedList) - 1) - len(customersUAV)

		availUAVs = {}
		for i in N_zero:
			availUAVs[i] = list(V)

		# Create UAV sorties for each UAV customer:
		for j in SortedCust[tmpMaxSkip]:

			Waiting = -10*bigM

			sortie = []

			for abc in range(0 , min(tmpMaxSkip,totalNumSkipsAllowed)+1):

				for [v,i,k] in UAVCustSupport[abc][j]:
					tempp = myOrderedList.index(i)
					tempq = myOrderedList.index(k)
					availability = True
					for tempindex in range(tempp,tempq):
						if v not in availUAVs[myOrderedList[tempindex]]:
							availability = False
							break

					if availability == True:
						tempWaiting = (tauprimeF[v][i][j] + node[j].serviceTimeUAV + tauprimeE[v][j][k]) - (t[k] - t[i])

						if tempWaiting < 0:
							if tempWaiting > Waiting:
								Waiting = tempWaiting
								sortie = [v,i,j,k]

						else:
							if Waiting < 0:
								Waiting = tempWaiting
								sortie = [v,i,j,k]
							else:
								if Waiting > tempWaiting:
									Waiting = tempWaiting
									sortie = [v,i,j,k]

			# If no sortie is found for customer j, append it to the list bigZ:
			if len(sortie) == 0:
				if tmpMaxSkip == 0:
					bigZ[tmpMaxSkip+maxSkip+1].append(j)
				else:
					del myY[tmpMaxSkip+maxSkip+1]
					del bigZ[tmpMaxSkip+maxSkip+1]
					break

			else:
				myY[tmpMaxSkip+maxSkip+1].append(sortie)
				tempp = myOrderedList.index(sortie[1])
				tempq = myOrderedList.index(sortie[3])

				totalNumSkipsAllowed = totalNumSkipsAllowed - (tempq-tempp-1)

				for tempindex in range(tempp,tempq):
					availUAVs[myOrderedList[tempindex]].remove(sortie[0])


	# Only pass unique UAV tours:
	UniqueMyY = []
	UniqueBigZ = []

	for i in myY:
		if myY[i] not in UniqueMyY:
			UniqueMyY.append(list(myY[i]))
			UniqueBigZ.append(list(bigZ[i]))


	#------------------------ALGORITHM 8 (Find a UAV customer to insert into truck tour if no feasible sortie assignments found) STARTS HERE-----------------------#

	# Reset bigZ
	bigZ = []
	for i in UniqueBigZ:
		for j in i:
			if j not in bigZ:
				bigZ.append(j)
		
	# If there are infeasible customers (len(bigZ) > 0),				
	# we're only going to return only one bigZ customer with the lowest insertCost
	insertTuple = []
	myInsertCost = []
	myZ = []

	if (len(bigZ) == 0):	# No infeasible customers
		for i in range(0,len(UniqueMyY)):
			myInsertCost.append(0)
			insertTuple.append({})
			myZ.append([])

	else:
		cInsert = defaultdict(make_dict)
		cWait = defaultdict(make_dict)
		cFail = defaultdict(make_dict)

		for i in C:
			for p in range(1, len(myOrderedList)):
				# Create a TSP route by inserting UAV customer i into the input TSP tour:
				tmpRoute = myOrderedList[0:p] + [i] + myOrderedList[p:len(myOrderedList)]
				
				# Is this TSP route unique?
				if (tmpRoute not in prevTSPtours):
				
					cInsert[i][p] = tau[myOrderedList[p-1]][i] + tau[i][myOrderedList[p]] - tau[myOrderedList[p-1]][myOrderedList[p]]
					
					for j in bigZ:
						isFeas = False
						tmp = float('inf')
						
						if (j == i):
							# We're just going to insert j into 
							isFeas = True
							tmp = 0.0
							cWait[i][p][j] = 0.0
							cFail[i][p][j] = 0.0
						else:
							# Find the maximum possible endurance for this v,i,j combination:
							eeeMax = max(eee[v][i][j].values())

							# Could we launch from i?
							truckTime = 0.0		# We'll find the total time to travel from i to some changing k
							iprime = i
							prevk = 0
							for pprime in range(p, len(myOrderedList)):
								k = myOrderedList[pprime]
								truckTime += tau[iprime][k]		# Time to travel from iprime to k
								iprime = k
								if (prevk):
									truckTime += sigma[prevk]	# Time to serve intermediate customers
								prevk = k
								
								if truckTime <= eeeMax:
									if ((tauprimeF[v][i][j] + sigmaprime[j] + tauprimeE[v][j][k] <= eee[v][i][j][k]) and (truckTime <= eee[v][i][j][k])):
										isFeas = True
										
										if (max(0, tauprimeF[v][i][j] + sigmaprime[j] + tauprimeE[v][j][k] - truckTime) < tmp):
											tmp = max(0, tauprimeF[v][i][j] + sigmaprime[j] + tauprimeE[v][j][k] - truckTime)
								else:
									break

							# Find the maximum possible endurance for this v,i,j combination:
							eeeMax = 0
							for k in eee[v]:
								if ((k != i) and (k != j) and (node[j].parcelWtLbs <= vehicle[v].capacityLbs)):
									if eeeMax < eee[v][k][j][i]:
										eeeMax = eee[v][k][j][i]

							# Could we launch from k?
							truckTime = 0.0		# We'll find the total time to travel from some changing k to i
							iprime = i
							prevk = 0						
							for pprime in range(p-1, 0-1, -1):
								k = myOrderedList[pprime]
								truckTime += tau[k][iprime]
								iprime = k
								if (prevk):
									truckTime += sigma[prevk]
								prevk = k
								
								if truckTime <= eeeMax:							
									if ((tauprimeF[v][k][j] + sigmaprime[j] + tauprimeE[v][j][i] <= eee[v][k][j][i]) and (truckTime <= eee[v][k][j][i])):
										isFeas = True
										
										if (max(0, tauprimeF[v][k][j] + sigmaprime[j] + tauprimeE[v][j][i] - truckTime) < tmp):
											tmp = max(0, tauprimeF[v][k][j] + sigmaprime[j] + tauprimeE[v][j][i] - truckTime)
								else:
									break
	
							# Update costs
							if (isFeas):
								cWait[i][p][j] = tmp
								cFail[i][p][j] = 0.0
							else:
								cWait[i][p][j] = 0.0
								cFail[i][p][j] = insertCost[j]


		bigZ = None
		for bigZ in UniqueBigZ:
			if len(bigZ) == 0:
				myInsertCost.append(0)
				insertTuple.append({})
				myZ.append([])

			else:
				bestCost = float('inf')
				bestIPcombo = []

				for i in cInsert:
					for p in cInsert[i]:

						if i in bigZ:
							tmpcInsert = cInsert[i][p]
						else:
							tmpcInsert = cInsert[i][p]*1.5

						tmpcWait = 0.0
						tmpcFail = 0.0

						for j in bigZ:
							tmpcWait +=	cWait[i][p][j]
							tmpcFail += cFail[i][p][j]		
		
						if (tmpcInsert + tmpcWait + tmpcFail < bestCost):
							bestCost = tmpcInsert + tmpcWait + tmpcFail
							bestIPcombo = [i, p]			

				# We're going to insert customer j in the truck's route between customers i and k:
				p = bestIPcombo[1]		# Position
				j = bestIPcombo[0]		# Inserted customer
				i = myOrderedList[p-1]	# Customer before j
				k = myOrderedList[p]	# Customer after j
				
				myInsertCost.append(insertCost[j])
				insertTuple.append({'j': j, 'i': i, 'k': k})
				myZ.append([j])

	return (myInsertCost, myX, UniqueMyY, myZ, insertTuple)