module analysis::m3::tests::CoreTester

import analysis::m3::Core;
import lang::Syntax;
import lang::Parser;
import ParseTree;

import util::TestUtils;

// Lib tests
public Module testModule = setDecls(parseModule("module account.AccountLib
    
import account.saving.SavingsAccount
    
invariant positiveBalance {
    this.balance \>= EUR 0.00;
}
            
event close() {
    preconditions {
        this.balance == EUR 0.00;
    }
}

event block() {}
event block2() {}
event unblock() {}
event destroy() {}

function singleInterest(balance: Money, interest: Percentage): Money =  (balance / 100) * interest;
"));

public Module creditBookingLib = setDecls(parseModule(|project://rebel-core/tests/booking/sepa/dd/CreditBookingLib.ebl|));

test bool testModul() = eq(m.decl, |rebel+module:///account.AccountLib|) 
    when /Module m := testModule;
    
test bool testLib() = eq(m.decl, |rebel+lib:///account.AccountLib|) 
    when /LibraryModules m := testModule;

test bool testImport() = eq(i.decl, |rebel+import:///account.saving.SavingsAccount|)
    when /Import i := testModule;
         
test bool testEventDef() = eq(e.decl, |rebel+event:///account.AccountLib/close|)
    when /EventDef e := testModule; //  why does this work? It should only work for the first event (or I guess last in this case)
    
test bool testInvariantDef() = eq(id.decl, |rebel+invariant:///account.AccountLib/positiveBalance|)  
    when /InvariantDef id := testModule;
    
test bool testFunctionDef() = eq(fd.decl, |rebel+function:///account.AccountLib/singleInterest|)
    when /FunctionDef fd := testModule;

// Specification tests
public Module creditBooking = setDecls(parseModule("module booking.sepa.dd.CreditBooking

import booking.sepa.dd.CreditBookingLib

// BookCreditorAccount Booking is booked from a single WashAccount.
specification CreditBooking {
    fields {
        id: Integer @key
        creditor: IBAN
        settlementDate: Date
        globalCredit: Money
    }
    
    events {
        create[]
        book[]
        fail[]
        revoke[]
    }
    
    invariants {
        positiveBalance
    }   
    
    lifeCycle {
        initial init    -\> initialized: create
        initialized     -\> successful: book
                        -\> failed: fail
                        -\> revoked: revoke
        final revoked
        final successful
        final failed
    }
}"));

test bool testModul() = eq(m.decl, |rebel+module:///booking.sepa.dd.CreditBooking|) 
    when /Module m := creditBooking;
    
// TODO is this correct? Why is the name of the specification also part of the module
test bool testSpec() = eq(s.decl, |rebel+specification:///booking.sepa.dd.CreditBooking/CreditBooking|) 
    when /Specification s := creditBooking;
    
test bool testField() = eq(f.decl, |rebel+field:///booking.sepa.dd.CreditBooking/CreditBooking/id|) 
    when /FieldDecl f := creditBooking;
    
test bool testEventRef() = eq(er.decl, |rebel+eventRef:///booking.sepa.dd.CreditBooking/CreditBooking/create|) 
    when /EventRef er := creditBooking;

test bool testInvariantRef() = eq(ir.decl, |rebel+invariantRef:///booking.sepa.dd.CreditBooking/CreditBooking/positiveBalance|) 
    when /InvariantRef ir := creditBooking;
    
test bool testStateDef() = eq(sd.decl, |rebel+state:///booking.sepa.dd.CreditBooking/CreditBooking/init|) 
    when /StateFrom sd := creditBooking;

// Generic
loc modul = |rebel+module:///account.savings.SavingsAccount|;

// Specification
loc spec = |rebel+specification:///account.savings.SavingsAccount|;

public loc field = |rebel+field:///account.savings.SavingsAccount/balance|;
public loc eventRef = |rebel+eventRef:///account.savings.SavingsAccount/create|; // TODO maybe add config parameters
public loc invariantRef = |rebel+invariantRef:///account.savings.SavingsAccount/positiveBalance|;
public loc stateDef = |rebel+state:///account.savings.SavingsAccount/init|; 

// Lib
public loc lib = |rebel+lib:///accounts.savings.AccountLib|; // List of LibraryModule
public loc event = |rebel+event:///accounts.savings.AccountLib/create|; 
public loc param = |rebel+param:///accounts.savings.AccountLib/create/id|; // For event config params, event transition params, function params, keyword params
public loc function = |rebel+function:///accounts.savings.AccountLib/functionName|;
public loc invariant = |rebel+invariant:///accounts.savings.AccountLib/invariantName|;