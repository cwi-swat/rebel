var specs = [ 
	{ 
		"fqn":"booking.sepa.ct.OnUsCreditTransfer",  
		"name":"OnUsCreditTransfer", 
		"documentation":"", 
		"modifier":"", 
		"inheritsFrom": {}, 
		"extendedBy":[], 
		"fields":[{"name":"amount", "type":"Money"}, 
		          {"name":"beneficiaryAccount", "type":"IBAN"}, 
		          {"name":"orderingAccount", "type":"IBAN"}, 
		          {"name":"receivedTime", "type":"DateTime"}, 
		          {"name":"id", "type":"Integer"}, 
		          {"name":"actualExecutionDate", "type":"Date"}, 
		          {"name":"requestedExecutionDate", "type":"Date"}], 
		"events":[{ 
		          	"id": "event_init_create_accepted", 
		          	"label": "create", 
		          	"doc": "Create a new Sepa CT on us credit transfer", 
		          	"config": [{"name":"sepaCountryCodes", "type":"set[String]", "value":"= {\"NL\",\"BE\",\"DE\",\"FR\"}"}], 
		           	"params": [{"name":"id", "type":"Integer"},{"name":"orderingAccount", "type":"IBAN"},{"name":"beneficiaryAccount", "type":"IBAN"},{"name":"requestedExecutionDate", "type":"Date"},{"name":"amount", "type":"Money"}], 
		           	"preconditions": [{"doc":"SEPA CT only accepts EUR payments, TODO: What is the maximum allowed amount?", "code":"amount.currency == EUR"},{"code":"amount > EUR 0.00;"},{"doc":"The executionDate must be within 183 days of the received date and can be maximum 5 days in the past", "code":"requestedExecutionDate - now.date <= 183 Day"},{"code":"now.date - requestedExecutionDate <= 5 Day;"},{"code":"beneficiaryAccount.countryCode in {\"NL\",\"BE\",\"DE\",\"FR\"};"},{"code":"orderingAccount.countryCode in {\"NL\",\"BE\",\"DE\",\"FR\"};"},{"code":"orderingAccount.countryCode == beneficiaryAccount.countryCode;"},{"code":"initialized CurrentAccount[orderingAccount];"},{"code":"initialized CurrentAccount[beneficiaryAccount];"}], 
		           	"postconditions": [{"code":"new this.orderingAccount == orderingAccount;"},{"code":"new this.beneficiaryAccount == beneficiaryAccount;"},{"code":"new this.requestedExecutionDate == requestedExecutionDate;"},{"doc":"If the requested received date lies before the current date (now) than set it to today, otherwise use the requested execution date as the actual execution date", "code":"new this.actualExecutionDate == nextCorrectExecutionDate(requestedExecutionDate, now.date)"},{"code":"new this.receivedTime == now;"},{"code":"new this.amount == amount;"}], 
		           	"sync": [] 
		          	}, 
		          { 
		          	"id": "event_accepted_cancel_cancelled", 
		          	"label": "cancel", 
		          	"doc": "Cancellation of the order happens outside the scope of the order entity itself and therefore does not contain any extra constraints", 
		          	"config": [], 
		           	"params": [], 
		           	"preconditions": [], 
		           	"postconditions": [], 
		           	"sync": [] 
		          	}, 
		          { 
		          	"id": "event_authorized_send_sent", 
		          	"label": "send", 
		          	"doc": "Send triggers the actual wiring of money between the accounts.", 
		          	"config": [], 
		           	"params": [], 
		           	"preconditions": [{"doc":"The order can only be executed on the execution date", "code":"now.date == this.actualExecutionDate"}], 
		           	"postconditions": [], 
		           	"sync": [{"doc":"Withdraw the money from the ordering account", "code":"CurrentAccount[this.orderingAccount].withdraw(this.amount)"},{"doc":"Deposit the money to the beneficiary account", "code":"CurrentAccount[this.beneficiaryAccount].deposit(this.amount)"}] 
		          	}, 
		          { 
		          	"id": "event_accepted_authorize_authorized", 
		          	"label": "authorize", 
		          	"doc": "Authorization of the order happens outside the scope of the order entity itself and therefore does not contain any extra constraints", 
		          	"config": [], 
		           	"params": [], 
		           	"preconditions": [], 
		           	"postconditions": [], 
		           	"sync": [] 
		          	}, 
		          { 
		          	"id": "event_authorized_cancel_cancelled", 
		          	"label": "cancel", 
		          	"doc": "Cancellation of the order happens outside the scope of the order entity itself and therefore does not contain any extra constraints", 
		          	"config": [], 
		           	"params": [], 
		           	"preconditions": [], 
		           	"postconditions": [], 
		           	"sync": [] 
		          	}, 
		          { 
		          	"id": "event_authorized_reject_rejected", 
		          	"label": "reject", 
		          	"doc": "A order can be rejected if for instance it is not possible to withdraw the amount from the ordering account", 
		          	"config": [], 
		           	"params": [], 
		           	"preconditions": [], 
		           	"postconditions": [], 
		           	"sync": [] 
		          	}], 
		"states":[{"id":"state_init", "label": "", "initial": true}, 
		          {"id":"state_accepted", "label":"accepted"}, 
		          {"id":"state_rejected", "label":"", "final": true}, 
		          {"id":"state_cancelled", "label":"", "final": true}, 
		          {"id":"state_authorized", "label":"authorized"}, 
		          {"id":"state_sent", "label":"", "final": true}], 
		"transitions":[{"from":"state_authorized", "to":"state_rejected", "via":"event_authorized_reject_rejected"}, 
		               {"from":"state_accepted", "to":"state_authorized", "via":"event_accepted_authorize_authorized"}, 
		               {"from":"state_authorized", "to":"state_cancelled", "via":"event_authorized_cancel_cancelled"}, 
		               {"from":"state_authorized", "to":"state_sent", "via":"event_authorized_send_sent"}, 
		               {"from":"state_init", "to":"state_accepted", "via":"event_init_create_accepted"}, 
		               {"from":"state_accepted", "to":"state_cancelled", "via":"event_accepted_cancel_cancelled"}], 
		"externalMachines":[{"id":"externalmachine_CurrentAccount", "label":"CurrentAccount", "url":"?", "referenceType":"out"}], 
		"transitionsToExternalMachines":[{"from":"event_authorized_send_sent", "to":"externalmachine_CurrentAccount", "toEvent":"event_withdraw"}, 
		                                 {"from":"event_authorized_send_sent", "to":"externalmachine_CurrentAccount", "toEvent":"event_deposit"}, 
		                                 {"from":"event_init_create_accepted", "to":"externalmachine_CurrentAccount"}], 
		"transitionsFromExternalMachines":[] 
	} 
]; 
