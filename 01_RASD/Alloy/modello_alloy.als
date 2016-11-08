sig wUsername {}{ //Signatura che rappresenta l'username di un utente
	all uname : wUsername | //Gli username genertai sono necessariamente associati ad uno ed un solo utente
		one u : User | u.username = uname 
}

one sig Company{
	vehicles: some Vehicle,
	availableVehicles: set Vehicle,
	notAvailableVehicles: set Vehicle,
	reservedVehicles: set Vehicle,
	rentedVehicles: set Vehicle
}{ no v : Vehicle | vehicles - v = vehicles //I veicoli del mondo sono solo veicoli della compagnia
	(vehicles = availableVehicles+notAvailableVehicles+reservedVehicles+rentedVehicles) and (availableVehicles&reservedVehicles = none and availableVehicles&notAvailableVehicles = none and reservedVehicles&notAvailableVehicles = none and rentedVehicles&notAvailableVehicles = none and availableVehicles&rentedVehicles = none and reservedVehicles&rentedVehicles = none) //I veicoli sono suddivisi in disponibili, prenotati, noleggiati e non esiste intersezione fra i gruppi
 }

sig SafeArea {}

sig User{
	username: one wUsername
}{ }

sig Vehicle{
	battery: one Int,
	safeArea: lone SafeArea
}{ battery >= 0 and battery <= 100}

fact{ //Facts about vehicles
	no v : Company.vehicles | (v in Company.availableVehicles or v in Company.reservedVehicles) and v.safeArea = none //Non possono esistere veicoli disponibili o prenotati fuori da una safe area perché il noleggio può essere terminato solo nelle safe area
	all v : Company.vehicles | v.battery < 20 => (v not in Company.availableVehicles and v not in Company.reservedVehicles)  //I veicoli con meno del 20% di batteria non sono disponibili e non può essere una reservatio su di loro
}

sig Reservation{
	user: one User,
	vehicle: one Vehicle
}{}

fact{ //Facts about reservations
	all v : Company.reservedVehicles | //Per ogni veicolo nel set dei veicoli riservati esiste una ed una solareservation
		one r : Reservation | r.vehicle = v

	all r : Reservation | //Per ogni reservation esiste uno ed un solo veicolo nel set dei veicoli riservati
		one v : Company.reservedVehicles | v = r.vehicle 
}

sig Rental{
	user: one User,
	vehicle: one Vehicle
}

fact{ //Facts about rentals
	all v : Company.rentedVehicles | //Per ogni veicolo nel set dei veicoli noleggiati esiste una ed una rental
		one r : Rental | r.vehicle = v

	all r : Rental | //Per ogni rental esiste uno ed un solo veicolo nel set dei veicoli noleggiati
		one v : Company.rentedVehicles | v = r.vehicle 
}

fact{ //Facts abot users' behaviours
	no disj r1, r2 : Reservation | r1.user = r2.user //Un utente non può prenotare più di un veicolo

	no disj r1, r2 : Rental | r1.user = r2.user //Un utente non può noleggiare più di un veicolo veicolo

	no ren : Rental, res : Reservation | ren.user = res.user //Un utente non può avere un noleggio ed una reservation contemporaneamente
}

pred show{}
run show for 5 but 8 int
