# This is a ZIMPL model file for Wait-and-see Recovery Robust Fleet Assignment Problem
# based on time-expanded multi-commodity flight network and Hamming recovery cost.
# Copyright @ 2020 Le Xuan Thanh - IM, VAST.
 
# Path to the folder containing data files
param pathToDataFolder := "C:\projects\FleetAssignmentIMH\FleetAssignmentIMH\MakeFleetAssignmentIMH\Data\";
 
# Input files
param fileAirports := pathToDataFolder + "Airports.txt";
param fileFleet    := pathToDataFolder + "FleetComponent.txt";
param fileFlights  := pathToDataFolder + "Flights.txt";
param fileEvents   := pathToDataFolder + "TimelineEvents.txt";
param fileAllInfo  := pathToDataFolder + "AssignmentData.txt";
param fileOldFA    := pathToDataFolder + "PreviousSolution.txt";
 
# Information about airports
set Airports := {read fileAirports as "<1s>" comment "#"};
param AirportCapacity[Airports] := read fileAirports as "<1s> 2n" comment "#";
 
# Information about fleet
set AircraftTypes := {read fileFleet as "<1s>" comment "#"};
param nAircraftsOfType[AircraftTypes] := read fileFleet as "<1s> 2n" comment "#";
 
## CONSTRUCTION OF THE TIME-EXPANDED MULTI-COMMODITY NETWORK
 
# The set of all nodes together with their increasing order with respect to event time
# Each member of this set has 4 components: order, airport, aircraft type, and date_time of event
set NodesWithOrder := {read fileEvents as "<1n, 2s, 3s, 4s>" comment "#"};
 
# Set of all nodes of the network (without their order)
# Each node has 3 components: airport, aircraft type, data_time of event
set Nodes := proj(NodesWithOrder, <2, 3, 4>);
 
# Set of forward ground arcs on the timelines associated with airports
set OrderedFGAs := {<i, aB, atB, tB, j, aE, atE, tE> in NodesWithOrder * NodesWithOrder with j == i + 1 and aB == aE and atB == atE};
set ForwardGroundArcs := proj(OrderedFGAs, <2,3,4,6,7,8>);
 
# Sets of the first nodes and the last nodes on timelines
set FirstAndLastOrderedNodes := {<i, aB, atB, tB, j, aE, atE, tE> in NodesWithOrder * NodesWithOrder with i == 1 and j == card(NodesWithOrder)};
set TimelineBridges := {<i, aB, atB, tB, j, aE, atE, tE> in NodesWithOrder * NodesWithOrder with j == i + 1 and (aB != aE or atB != atE)};
set FirstNodes := proj(TimelineBridges, <6, 7, 8>) + proj(FirstAndLastOrderedNodes, <2, 3, 4>);
set LastNodes := proj(TimelineBridges, <2, 3, 4>) + proj(FirstAndLastOrderedNodes, <6, 7, 8>);
 
# Set of backward ground arcs on the timelines associated with airports
set BackwardGroundArcs := {<aB, atB, tB, aE, atE, tE> in LastNodes * FirstNodes with aB == aE and atB == atE};
 
# Set of ground arcs
set GroundArcs := ForwardGroundArcs + BackwardGroundArcs;
 
# Set of flight arcs in the network
set DataForAssign := {read fileAllInfo as "<1s, 2s, 3s, 4s, 5s, 6s, 7n, 8n>" comment "#"};
set DepartReadyFlights := proj(DataForAssign, <1,2,3,5,6>);
set FlightArcs := {<aB, atB, tB, aE, atE, tE> in Nodes * Nodes with <aB, tB, aE, atB, tE> in DepartReadyFlights and atE == atB};
 
# Set of active flights (ones with possible assignments)
set RawFlights := {read fileFlights as "<1s, 2s, 3s>" comment "#"};
set ActiveFlights := RawFlights inter proj(FlightArcs, <1, 4, 3>);
 
## CONSTRUCTION FOR OBJECTIVE FUNCTION
set OldFASolution := {read fileOldFA as "<1s, 2s, 3s, 4s, 5s, 6s, 7n>" comment "#"};
set OldFlightArcs := proj(OldFASolution, <1,2,3,4,5,6>);
param xOld[OldFlightArcs] := read fileOldFA as "<1s, 2s, 3s, 4s, 5s, 6s> 7n" comment "#";
 
## VARIABLES
var x[FlightArcs + OldFlightArcs] binary;
var y[GroundArcs] >= 0;
 
## MODELING OBJECTIVE
minimize HammingCost: (sum <aB, atB, tB, aE, atE, tE> in OldFlightArcs: vabs(x[aB, atB, tB, aE, atE, tE] - xOld[aB, atB, tB, aE, atE, tE])) + (sum <aB, atB, tB, aE, atE, tE> in FlightArcs without OldFlightArcs: vabs(x[aB, atB, tB, aE, atE, tE]));
 
## MODELING CONSTRAINTS
 
# Variables of old indices that are no longer used in the new assignment must be zero
subto ZeroOld:
   forall <aB, atB, tB, aE, atE, tE> in OldFlightArcs without FlightArcs do
       x[aB, atB, tB, aE, atE, tE] == 0;
 
# Exactly one aircraft type is assigned to each active flight
subto AssignToActiveFlights:
	forall <aB, aE, tB> in ActiveFlights do
       sum <aB1, atB, tB1, aE1, atE, tE> in FlightArcs with aB1 == aB and tB1 == tB and aE1 == aE: x[aB1, atB, tB1, aE1, atE, tE] == 1;
 
# For each aircraft type, the number of used aircrafts is at most the number of available aircrafts
subto FleetCapacity:
	forall <at> in AircraftTypes do
		sum <aB, atB, tB, aE, atE, tE> in BackwardGroundArcs with atB == at: y[aB, atB, tB, aE, atE, tE] <= nAircraftsOfType[at];
 
# Flow conversation at each node
subto FlowConversation:
	forall <a, at, t> in Nodes do
		sum <a_fin, at_fin, t_fin> in Nodes with <a_fin, at_fin, t_fin, a, at, t> in FlightArcs: x[a_fin, at_fin, t_fin, a, at, t]
	  + sum <a_gin, at_gin, t_gin> in Nodes with <a_gin, at_gin, t_gin, a, at, t> in GroundArcs: y[a_gin, at_gin, t_gin, a, at, t]
    == sum <a_fout, at_fout, t_fout> in Nodes with <a, at, t, a_fout, at_fout, t_fout> in FlightArcs: x[a, at, t, a_fout, at_fout, t_fout]
	  + sum <a_gout, at_gout, t_gout> in Nodes with <a, at, t, a_gout, at_gout, t_gout> in GroundArcs: y[a, at, t, a_gout, at_gout, t_gout];
