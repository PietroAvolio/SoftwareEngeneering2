//----- SIGNATURES -----
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
	safeArea: lone SafeArea
}{ battery >= 0 and battery <= 100}

//Signatura che rappresenta una reservation
sig Reservation{
	user: one User,
	vehicle: one Vehicle,
	expired: one Bool,
	cancelled: one Bool,
	payment: lone Payment
}{
	expired = True <=> cancelled = False
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
	

//----- FACTS -----
 //Facts about vehicles
fact{
 	//Non possono esistere veicoli disponibili o prenotati fuori da una safe area perché il noleggio può essere terminato solo nelle safe area
	no v : Company.vehicles | (v in Company.availableVehicles or v in Company.reservedVehicles) and v.safeArea = none
	//I veicoli con meno del 20% di batteria non sono disponibili e non può esistere una reservatio su di loro
	all v : Company.vehicles | v.battery < 20 => (v not in Company.availableVehicles and v not in Company.reservedVehicles)  
}

 //Facts about reservations
fact{
	//Per ogni veicolo nel set dei veicoli riservati esiste una ed una sola reservation
	all v : Company.reservedVehicles | one r : Reservation | r.vehicle = v
	 //Per ogni reservation esiste uno ed un solo veicolo nel set dei veicoli riservati
	all r : Reservation | one v : Company.reservedVehicles | v = r.vehicle 
}

//Facts about rentals
fact{ 
	//Per ogni veicolo nel set dei veicoli noleggiati esiste una ed una rental
	all v : Company.rentedVehicles | one r : Rental | r.vehicle = v
	//Per ogni rental esiste uno ed un solo veicolo nel set dei veicoli noleggiati
	all r : Rental | one v : Company.rentedVehicles | v = r.vehicle 
	//Un noleggio non puo terminare fuori da una safe area
	no r : Rental | 	r.terminated = True and r.vehicle.safeArea = none
	 //Non esiste un noleggio terminato non associato ad un pagamento
	no r : Rental |	r.payment = none	and r.terminated = True
}

//Facts abot users
fact{ 
	//Un utente non può prenotare più di un veicolo allo stesso tempo
	no disj r1, r2 : Reservation | r1.user = r2.user
	//Un utente non può noleggiare più di un veicolo veicolo allo stesso tempo
	no disj r1, r2 : Rental | r1.user = r2.user 
	//Un utente non può avere un noleggio ed una reservation contemporaneamente
	no ren : Rental, res : Reservation | ren.user = res.user 
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

//----- ASSERTIONS -----

//---- PREDICATES -----
pred terminateRental(r, r': Rental){
	r'.user = r.user and r'.vehicle = r.vehicle and r'.duration = r.duration and r'.terminated = True and r'.payment != none
}

//----- RUN -----
pred show{}
run show for 8 int
run terminateRental
