----- SIGNATURES -----
abstract sig Bool {}
one sig True extends Bool {}
one sig False extends Bool {}

 //Signatura che rappresenta l'username di un utente
sig UserUsername {}{
 	//Gli username generati sono necessariamente associati ad uno ed un solo utente
	all uname : UserUsername | one u : User | u.username = uname 
}

//Signatura che rappresenta l'identificativo di un operatore
sig OperatorID{}{
	//Gli ID generati sono necessariamente associati ad uno ed un solo operatore
	all id : OperatorID |	one o : Operator | o.ID = id
}

//Signatura che rappresenta ShareEnJoy
one sig Company{
	vehicles: some Vehicle,
	availableVehicles: set Vehicle,
	notAvailableVehicles: set Vehicle,
	reservedVehicles: set Vehicle,
	rentedVehicles: set Vehicle,
	supportRequests: set SupportRequest,
	systemNotifications: set SystemNotification
}{
	//I veicoli del mondo sono solo veicoli della compagnia
	 no v : Vehicle | vehicles - v = vehicles 
	//I veicoli sono suddivisi in disponibili, non disponibili, prenotati, noleggiati e non esiste intersezione fra i gruppi
	(vehicles = availableVehicles+notAvailableVehicles+reservedVehicles+rentedVehicles) and (availableVehicles&reservedVehicles = none and availableVehicles&notAvailableVehicles = none and reservedVehicles&notAvailableVehicles = none and rentedVehicles&notAvailableVehicles = none and availableVehicles&rentedVehicles = none and reservedVehicles&rentedVehicles = none)
 }

//Signatura che rappresenta una SafeArea
sig SafeArea {}

//Signatura che rappresenta un utente
sig User{
	username: one UserUsername
}

//Signatura che rappresenta un veicolo
sig Vehicle{
	battery: one Int,
	safeArea: lone SafeArea,
	plugged: one Bool
}{battery >= 0 and battery <= 100}

//Signatura che rappresenta una reservation
sig Reservation{
	user: one User,
	vehicle: one Vehicle,
	expired: one Bool,
	cancelled: one Bool,
	payment: lone Payment
}{
	expired = True => cancelled = False
	//Se la reservation è scaduta o cancellata allora è associata ad un pagamento
	payment != none <=> (cancelled = True or expired = True)
}

//Signatura che rappresenta un noleggio
sig Rental{
	user: one User,
	vehicle: one Vehicle,
	terminated: one Bool,
	payment: lone Payment,
	duration: one Int
}{
	duration > 0
	//Se il noleggio non è terminato non è associato ad un pagamento
	payment != none <=> terminated = True
}

//Signatura che rappresenta un pagamento
sig Payment{
	amount: one Int,
	success: one Bool
}{
	amount > 0
	//I pagamenti vengono generati solo associati ai rental terminati o alle reservation scadute/cancellate
	all p : Payment | (one r : Rental | r.terminated = True and r.payment = p) or (one r : Reservation | (r.expired = True or r.cancelled = True) and r.payment = p)
}


//Signatura che rappresenta un operatore
sig Operator{
	ID : OperatorID
}

//Signatura che rappresenta una richiesta di supporto
sig SupportRequest{
	sentBy : one User,
	handledBy : one Operator
}

sig SystemNotification {
	//Alcune notifiche possono essere associate ad un operatore
	handledBy : lone Operator,
	//Una notifica può riguardare un veicolo
	vehicle: lone Vehicle,
	//Una notifica può riguardare un pagamento
	payment: lone Payment
}{ 
	//Una notifica non può riguardare un veicolo e un pagamento contemporaneamente
	vehicle != none <=> payment = none
} 
	

----- FACTS -----
 //Facts about vehicles
fact{
 	//Non possono esistere veicoli disponibili o prenotati fuori da una safe area perché il noleggio può essere terminato solo nelle safe area
	no v : Company.vehicles | (v in Company.availableVehicles or v in Company.reservedVehicles) and v.safeArea = none
	//I veicoli con meno del 20% di batteria non sono disponibili e non può esistere una reservatio su di loro
	all v : Company.vehicles | v.battery < 20 => (v not in Company.availableVehicles and v not in Company.reservedVehicles)  
	//Se un veicolo è sotto carica allora non è noleggiato
	all v : Company.vehicles | v.plugged = True <=> v not in Company.rentedVehicles
}

 //Facts about reservations
fact{
	//Per ogni veicolo nel set dei veicoli riservati esiste una ed una sola reservation non scaduta o cancellata
	all v : Company.reservedVehicles | one r : Reservation | r.vehicle = v and r.cancelled = False and r.expired = False
	 //Per ogni reservation esiste uno ed un solo veicolo nel set dei veicoli riservati
	all r : Reservation | (r.cancelled = False and r.expired = False) => (one v : Company.reservedVehicles | v = r.vehicle) 
}

//Facts about rentals
fact{ 
	//Per ogni veicolo nel set dei veicoli noleggiati esiste una ed una rental non terminata
	all v : Company.rentedVehicles | one r : Rental | r.vehicle = v and r.terminated = False
	//Per ogni rental esiste uno ed un solo veicolo nel set dei veicoli noleggiati
	all r : Rental | (r.terminated = False) => (one v : Company.rentedVehicles | v = r.vehicle) 
	//Un noleggio non puo terminare fuori da una safe area
	no r : Rental | 	r.terminated = True and r.vehicle.safeArea = none
	 //Non esiste un noleggio terminato non associato ad un pagamento
	no r : Rental |	r.payment = none	and r.terminated = True
}

//Facts abot users
fact{ 
	//Un utente non può prenotare più di un veicolo allo stesso tempo
	no disj r1, r2 : Reservation | r1.user = r2.user and r1.expired = False and r1.cancelled = False and r2.expired = False and r2.cancelled = False
	//Un utente non può noleggiare più di un veicolo veicolo allo stesso tempo
	no disj r1, r2 : Rental | r1.user = r2.user and r1.terminated = False and r2.terminated = False
	//Un utente non può avere un noleggio ed una reservation contemporaneamente
	no ren : Rental, res : Reservation | ren.user = res.user and ren.terminated = False and res.expired = False and res.cancelled = False
	//Un utente non puo avere due richieste di supporto allo stesso tempo
	no disj sr1, sr2 : SupportRequest | sr1.sentBy = sr2.sentBy
}

//Facts about payments
fact{
	//Un pagamento puo essere associato ad una sola reservation o noleggio
	all p : Payment | (one rental: Rental | rental.payment = p) => ((no rental2: Rental | rental2.payment = p) and (no reservation: Reservation | reservation.payment = p))
		and (one reservation: Reservation | reservation.payment = p) => ((no reservation2: Reservation | reservation2.payment = p) and (no rental: Rental | rental.payment = p))
}

//facts about notifications
fact{
	//Esiste una notifica per ogni veicolo NonDisponibile
	all nav : Company.notAvailableVehicles | one n : Company.systemNotifications | n.vehicle = nav
	//Esiste una notifica per ogni pagamento fallito
	all fp : Payment | fp.success = False => (one notif : Company.systemNotifications | notif.payment = fp)
	//Se una notifica è associata ad un pagamento allora è un pagamento fallito
	all n : Company.systemNotifications | n.payment != none => n.payment.success = False
}

----- ASSERTIONS -----
//Non esistono due utenti con lo stesso username
assert noSameUsername {
  	no disj u,v: User | u.username = v.username
}
check noSameUsername for 5

//Non esistono due operatori con lo stesso ID
assert noSameID{
	no disj o1, o2: Operator | o1.ID = o2.ID
}
check noSameID for 5

//Tutti i noleggi terminati sono associati ad un pagamento
assert noTerminatedRentalWithoutPayment {
  	no r: Rental | r.terminated = True && r.payment != none
}
check noTerminatedRentalWithoutPayment for 5

//Tutte le reservation scadute o cancellate sono associate ad un pagamento
assert noTerminatedReservationWithoutPayment{
	no r: Rental | r.terminated = True && r.payment != none
}
check noTerminatedReservationWithoutPayment for 5

//Un pagamento è associato ad un solo evento
assert onePaymentOneEvent{
	no disj r1, r2: Rental | r1.payment = r2.payment
	no disj r1, r2: Reservation | r1.payment = r2.payment
	no res: Reservation | some rent: Rental | res.payment = rent.payment
}
check onePaymentOneEvent for 5

//Un utente non puo avere due reservation attive, un veicolo non puo essere associato a due reservation attive
assert noMoreThanOneReservation{
	no disj r1, r2: Reservation | (r1.user = r2.user or r1.vehicle = r2.vehicle) and r1.cancelled = False and r2.cancelled = False and r1.expired = False and r2.expired = False
}
check noMoreThanOneReservation for 5

//Un utente non puo avere due noleggi attivi, un veicolo non puo essere associato a due noleggi attivi
assert noMoreThanOneRental{
	no disj r1, r2: Rental | (r1.user = r2.user or r1.vehicle = r2.vehicle) and r1.terminated = False and r2.terminated = False
}
check noMoreThanOneRental for 5

//Un utente non puo avere un noleggio ed una reservation attive allo stesso tempo, Un veicolo non puo essere associato ad una reservation ed un noleggio allo stesso tempo
assert noReservationAndRental{
	no u: User |
		(some rental: Rental | rental.user = u and rental.terminated = False) and (some reservation: Reservation | reservation.user = u and reservation.cancelled = False and reservation.expired = False)

	no v: Vehicle |
		(some rental: Rental | rental.vehicle = v and rental.terminated = False) and (some reservation: Reservation | reservation.vehicle = v and reservation.cancelled = False and reservation.expired = False)
}
check noReservationAndRental for 5

//Non può esistere un veicolo in carica e noleggiato
assert noChargingWhileDriving{
	no v: Vehicle | v in Company.rentedVehicles and v.plugged = True
}
check noChargingWhileDriving for 5

//Non puo esistere un veicolo disponibile fuori da una safe area
assert AlwaysSafe{
	no v: Vehicle | v in Company.availableVehicles and v.safeArea = none
}
check AlwaysSafe for 5

---- PREDICATES -----
pred show1{
	#User > 1
	#Reservation > 1
	#Rental > 1
	#Operator = 1
	#SupportRequest = 1
	#SystemNotification = 1
	some v : Vehicle | v.battery < 20
	some v: Vehicle | v.safeArea = none
	some v: Vehicle | v.plugged = True
	some p: Payment | p.success = False
}

pred smallScenario{
	#Vehicle <= 4
	#User <= 4
	#Operator = 1
	#SupportRequest = 0
	#Rental <= 4
	#Reservation <= 4
	some r : Rental | r.terminated = False
	some r : Reservation | r.cancelled = False and r.expired = False
}

run show1 for 6 but 8 int
run smallScenario for 6 but 8 int
