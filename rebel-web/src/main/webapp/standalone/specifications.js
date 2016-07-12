var specs = [ 
	{ 
		"fqn":"booking.sepa.ct.CreditTransfer",  
		"name":"CreditTransfer", 
		"documentation":"", 
		"modifier":"", 
		"inheritsFrom": {}, 
		"extendedBy":[], 
		"fields":[{"name":"executionDate", "type":"Date"}, 
		          {"name":"ordering", "type":"IBAN"}, 
		          {"name":"receiveDate", "type":"Date"}, 
		          {"name":"beneficiary", "type":"IBAN"}, 
		          {"name":"amount", "type":"Money"}], 
		"events":[{ 
		          	"id": "event_init_create_validated", 
		          	"label": "create", 
		          	"doc": "", 
		          	"config": [{"name":"sepaCountryCodes", "type":"set[String]", "value":"= {\"NL\",\"BE\",\"DE\",\"FR\"}"}], 
		           	"params": [{"name":"ordering", "type":"IBAN"},{"name":"beneficiary", "type":"IBAN"},{"name":"executionDate", "type":"Date"},{"name":"receiveDate", "type":"Date"},{"name":"amount", "type":"Money"}], 
		           	"preconditions": [{"doc":"SEPA CT only accepts EUR payments", "code":"amount.currency == EUR"},{"code":"amount > EUR 0.00;"},{"doc":"The executionDate must be within 5 days of the received date", "code":"executionDate >= receiveDate && executionDate - receiveDate <= 5 Day"},{"doc":"The received date can not be in the past", "code":"receiveDate >= now"},{"doc":"The involved accounts need to be in the SEPA zone", "code":"beneficiary.countryCode in {\"NL\",\"BE\",\"DE\",\"FR\"}"},{"code":"ordering.countryCode in {\"NL\",\"BE\",\"DE\",\"FR\"};"}], 
		           	"postconditions": [{"code":"new this.ordering == ordering;"},{"code":"new this.beneficiary == beneficiary;"},{"code":"new this.executionDate == executionDate;"},{"code":"new this.receiveDate == receiveDate;"},{"code":"new this.amount == amount;"},{"code":"new this.currency == currency;"}], 
		           	"sync": [] 
		          	}], 
		"states":[{"id":"state_validated", "label":"validated"}, 
		          {"id":"state_init", "label": "", "initial": true}], 
		"transitions":[{"from":"state_init", "to":"state_validated", "via":"event_init_create_validated"}], 
		"externalMachines":[], 
		"transitionsToExternalMachines":[], 
		"transitionsFromExternalMachines":[] 
	} 
]; 
