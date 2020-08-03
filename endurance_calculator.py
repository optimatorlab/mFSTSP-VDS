from collections import defaultdict
import math
from scipy.optimize import brentq

def make_dict():
	return defaultdict(make_dict)

	# Usage:
	# tau = defaultdict(make_dict)
	# v = 17
	# i = 3
	# j = 12
	# tau[v][i][j] = 44

def Pi(T, Vvert):
	return 0.8554*T*(Vvert/2.0 + math.sqrt((Vvert/2.0)**2 + T/(0.3051)**2))

def Pp(T):
	return 0.3177*(T**1.5)

def Ppar(Vair):
	return 0.0296*(Vair**3)

def Thrust(m, Vair):  # MATTERNET M2 Weight without payload: 9.5 Kg
	return math.sqrt(((1.5 + m)*9.8 - 0.0279*(Vair*math.cos(10*math.pi/180.0))**2)**2 + (0.0296*Vair**2)**2)

def SpeedFunction(m, Vair, distance, energy_left):
	newT = Thrust(m, Vair)
	return (distance/float(Vair))*(Pi(newT, 0) + Pp(newT) + Ppar(Vair)) - (energy_left - 0.00001)


def give_endurance(node, vehicle, travel, v, i, j, k, totalTimeij, totalTimejk, speedij, speedjk):

	# for [v,i,j,k] in P:
	p 		= vehicle[v].takeoffSpeed
	qij 	= speedij
	qjk 	= speedjk
	r 		= vehicle[v].landingSpeed
	TTvij 	= travel[v][i][j].takeoffTime
	FTvij 	= totalTimeij - travel[v][i][j].takeoffTime - travel[v][i][j].landTime
	LTvij 	= travel[v][i][j].landTime

	TTvjk 	= travel[v][j][k].takeoffTime
	FTvjk 	= totalTimejk - travel[v][j][k].takeoffTime - travel[v][j][k].landTime
	LTvjk 	= travel[v][j][k].landTime
	sj = node[j].serviceTimeUAV
	mj = (node[j].parcelWtLbs)*0.453592   # Weight in Kg
	E = vehicle[v].batteryPower

	minimum_time_required = TTvij + FTvij + LTvij + sj + TTvjk + FTvjk + LTvjk

	# a) Takeoff from customer i:
	newT = Thrust(mj, 0)
	Ea = TTvij*(Pi(newT, p) + Pp(newT))

	# b) Fly to customer j:
	newT = Thrust(mj, qij)
	Eb = FTvij*(Pi(newT, 0) + Pp(newT) + Ppar(qij))

	# c) Land at customer j:
	newT = Thrust(mj, 0)
	Ec = LTvij*(Pi(newT, r) + Pp(newT))

	# d) Takeoff from customer j:
	newT = Thrust(0, 0)
	Ed = TTvjk*(Pi(newT, p) + Pp(newT))

	# e) Fly to customer k:
	newT = Thrust(0, qjk)
	Ee = FTvjk*(Pi(newT, 0) + Pp(newT) + Ppar(qjk))

	# f) Land at customer k:
	newT = Thrust(0, 0)
	Ef = LTvjk*(Pi(newT, r) + Pp(newT))

	minimum_energy_required = Ea + Eb + Ec + Ed + Ee + Ef

	energy_left = E - minimum_energy_required

	if energy_left >= 0:
		newT = Thrust(0, 0)
		PHover = Pi(newT, 0) + Pp(newT)

		endurance = minimum_time_required + float(energy_left)/PHover

	else:
		endurance = -1
	
	return endurance
	# return 1200


def modify_speed(oldLaunchTime, oldLandTime, newLaunchTime, newLandTime, v, i, j, k, node, vehicle, travel, totalTimeij, totalTimejk, speedij, speedjk):
	oldDuration = oldLandTime - oldLaunchTime - vehicle[v].recoveryTime
	newDuration = newLandTime - newLaunchTime - vehicle[v].recoveryTime

	# for [v,i,j,k] in P:
	p 		= vehicle[v].takeoffSpeed
	r 		= vehicle[v].landingSpeed
	TTvij 	= travel[v][i][j].takeoffTime
	FTvij 	= totalTimeij - travel[v][i][j].takeoffTime - travel[v][i][j].landTime
	LTvij 	= travel[v][i][j].landTime

	TTvjk 	= travel[v][j][k].takeoffTime
	FTvjk 	= totalTimejk - travel[v][j][k].takeoffTime - travel[v][j][k].landTime
	LTvjk 	= travel[v][j][k].landTime
	sj = node[j].serviceTimeUAV
	mj = (node[j].parcelWtLbs)*0.453592   # Weight in Kg
	E = vehicle[v].batteryPower

	# a) Takeoff from customer i:
	newT = Thrust(mj, 0)
	Ea = TTvij*(Pi(newT, p) + Pp(newT))

	# b) Fly to customer j:
	newT = Thrust(mj, speedij)
	Eb = FTvij*(Pi(newT, 0) + Pp(newT) + Ppar(speedij))

	# c) Land at customer j:
	newT = Thrust(mj, 0)
	Ec = LTvij*(Pi(newT, r) + Pp(newT))

	# d) Takeoff from customer j:
	newT = Thrust(0, 0)
	Ed = TTvjk*(Pi(newT, p) + Pp(newT))

	# f) Land at customer k:
	newT = Thrust(0, 0)
	Ef = LTvjk*(Pi(newT, r) + Pp(newT))

	energy_spent = Ea + Eb + Ec + Ed + Ef

	energy_left = E - energy_spent


	# We have to find the required FTvjk:
	newFTvjk = newDuration - totalTimeij - sj - TTvjk - LTvjk
	if newFTvjk >= 0:
		newspeedjk = speedjk*FTvjk/float(newFTvjk)
		changeij = False
	else:
		newspeedjk = float(vehicle[v].cruiseSpeed)
		newFTvjk = speedjk*FTvjk/float(newspeedjk)
		changeij = True

	# Modify the speed of j -> k leg first:

	# See if the speed is more than its maximum possible value:
	if newspeedjk > vehicle[v].cruiseSpeed:
		newspeedjk = float(vehicle[v].cruiseSpeed)
		newFTvjk = speedjk*FTvjk/float(newspeedjk)
		changeij = True

	# Find the energy requirement associated with flying from j to k with new speed:
	newT = Thrust(0, newspeedjk)
	Ee = newFTvjk*(Pi(newT, 0) + Pp(newT) + Ppar(newspeedjk))

	# See if the drone has enough energy left to fly at this speed:
	if Ee > energy_left:
		# Find a new speed:
		if SpeedFunction(0, speedjk, speedjk*FTvjk, energy_left) < 0:
			newspeedjk = brentq(lambda actVar: SpeedFunction(0, actVar, speedjk*FTvjk, energy_left), speedjk, vehicle[v].cruiseSpeed)
		elif SpeedFunction(0, speedjk, speedjk*FTvjk, energy_left) < 0.00001:
			newspeedjk = float(speedjk)
		else:
			print("ERROR: Energy calculation wrong. Exiting...")
			exit()
		newFTvjk = speedjk*FTvjk/float(newspeedjk)
		newT = Thrust(0, newspeedjk)
		Ee = newFTvjk*(Pi(newT, 0) + Pp(newT) + Ppar(newspeedjk))
		changeij = False


	# Modify the speed of i -> j leg, if necessary:
	newFTvij = float(FTvij)
	newspeedij = float(speedij)

	if changeij == True:

		newFTvij = newDuration - TTvij - LTvij - sj - TTvjk - newFTvjk - LTvjk
		if newFTvij >= 0:
			newspeedij = speedij*FTvij/float(newFTvij)
		else:
			newspeedij = float(vehicle[v].cruiseSpeed)
			newFTvij = speedij*FTvij/float(newspeedij)

		# See if the speed is more than its maximum possible value:
		if newspeedij > vehicle[v].cruiseSpeed:
			newspeedij = float(vehicle[v].cruiseSpeed)
			newFTvij = speedij*FTvij/float(newspeedij)

		# Find the energy requirement associated with flying from i to j with new speed:
		newT = Thrust(mj, newspeedij)
		Eb = newFTvij*(Pi(newT, 0) + Pp(newT) + Ppar(newspeedij))

		energy_left = E - (Ea + Ec + Ed + Ee + Ef)

		# See if the drone has enough energy left to fly at this speed:
		if Eb > energy_left:
			# Find a new speed:
			if SpeedFunction(mj, speedij, speedij*FTvij, energy_left) < 0:
				newspeedij = brentq(lambda actVar: SpeedFunction(mj, actVar, speedij*FTvij, energy_left), speedij, vehicle[v].cruiseSpeed)
			elif SpeedFunction(mj, speedij, speedij*FTvij, energy_left) < 0.00001:
				newspeedij = float(speedij)
			else:
				print("ERROR: Energy calculation wrong. Exiting...")
				exit()			
			newFTvij = speedij*FTvij/float(newspeedij)
			newT = Thrust(mj, newspeedij)
			Eb = newFTvij*(Pi(newT, 0) + Pp(newT) + Ppar(newspeedij))

	# As a last check, see if energy consumed is less than energy available:
	if Ea + Eb + Ec + Ed + Ee + Ef - E > 0:
		print("Energy calculation wrong. Exiting...")
		exit()

	# Other checks:
	if newFTvij <= 0:
		print("wrong i->j calculation. Exiting...")
		exit()

	if newFTvjk <= 0:
		print("wrong j->k calculation. Exiting...")
		exit()

	if (round(newspeedij,5) < round(speedij,5)) or (round(newspeedij,5) > round(vehicle[v].cruiseSpeed,5)):
		print("wrong i->j speed calculation. Exiting...")
		exit()

	if (round(newspeedjk,5) < round(speedjk,5)) or (round(newspeedjk,5) > round(vehicle[v].cruiseSpeed,5)):
		print("wrong j->k speed calculation. Exiting...")
		exit()

	checktprime_at_j = newLaunchTime + TTvij + newFTvij + LTvij
	hattprime_at_j = checktprime_at_j + sj
	checktprime_at_k = hattprime_at_j + TTvjk + newFTvjk + LTvjk + vehicle[v].recoveryTime

	newtotalTimeij = TTvij + newFTvij + LTvij
	newtotalTimejk = TTvjk + newFTvjk + LTvjk
		

	return [checktprime_at_j, hattprime_at_j, checktprime_at_k, newtotalTimeij, newtotalTimejk, newspeedij, newspeedjk]



def EndSpecs(node, vehicle, travel, v, i, j, k, distij, distjk, speedij, speedjk, idletime):

	# for [v,i,j,k] in P:
	p 		= vehicle[v].takeoffSpeed
	qij 	= speedij
	qjk 	= speedjk
	r 		= vehicle[v].landingSpeed
	TTvij 	= travel[v][i][j].takeoffTime
	FTvij 	= distij/float(speedij)
	LTvij 	= travel[v][i][j].landTime

	TTvjk 	= travel[v][j][k].takeoffTime
	FTvjk 	= distjk/float(speedjk)
	LTvjk 	= travel[v][j][k].landTime
	sj = node[j].serviceTimeUAV
	mj = (node[j].parcelWtLbs)*0.453592   # Weight in Kg
	E = vehicle[v].batteryPower

	minimum_time_required = TTvij + FTvij + LTvij + sj + TTvjk + FTvjk + LTvjk

	# a) Takeoff from customer i:
	newT = Thrust(mj, 0)
	Ea = TTvij*(Pi(newT, p) + Pp(newT))

	# b) Fly to customer j:
	newT = Thrust(mj, qij)
	Eb = FTvij*(Pi(newT, 0) + Pp(newT) + Ppar(qij))

	# c) Land at customer j:
	newT = Thrust(mj, 0)
	Ec = LTvij*(Pi(newT, r) + Pp(newT))

	# d) Takeoff from customer j:
	newT = Thrust(0, 0)
	Ed = TTvjk*(Pi(newT, p) + Pp(newT))

	# e) Fly to customer k:
	newT = Thrust(0, qjk)
	Ee = FTvjk*(Pi(newT, 0) + Pp(newT) + Ppar(qjk))

	# f) Land at customer k:
	newT = Thrust(0, 0)
	Ef = LTvjk*(Pi(newT, r) + Pp(newT))

	minimum_energy_required = Ea + Eb + Ec + Ed + Ee + Ef

	energy_left = E - minimum_energy_required

	if energy_left >= 0:
		newT = Thrust(0, 0)
		PHover = Pi(newT, 0) + Pp(newT)

		endurance = minimum_time_required + float(energy_left)/PHover

	else:
		endurance = -1

	enduranceUsed = minimum_time_required + idletime

	energyUsed = minimum_energy_required + PHover*idletime

	return [endurance, minimum_time_required, enduranceUsed, minimum_energy_required, energyUsed]