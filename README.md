# Rebel

## Introduction

Rebel is a domain specific specification language. It targets the financial domain. The language and its tooling was developed for the banking domain. Rebel is a generic language but has domain specific types like `Money` and `IBAN`. These types make it more natural to express constraints often found in the banking domain.

In essence a Rebel specification describes an entity and its accompanying state machine. The transitions in the state machine (events) are guarded. Data changes are declarative specified using pre- and postconditions on the events. Invariants guard the overall state. Communication between specifications is done using event synchronisation. 

Rebel specifications can be visualized, simulated and checked. Simulation and checking is done using the SMT solver Z3.

## Running Rebel
### Prerequisist
Rebel is build with the Rascal Language Workbench. To build Rebel Rascal needs to be in place as well. Currently Rebel and Rascal only work from inside the Eclipse IDE.

### Steps:
* Install Eclipse. Go to www.eclipse.org and download the latest version of Eclipse.
* Install Rascal. Go to [http://www.rascal-mpl.org] for instructions on how to install Rascal
* Clone this repo to your local workspace
* In Eclipse, with the Rascal perspective selected, import exising projects and import all Rebel projects
* Restart Eclipse

If you now open a Rebel specification (with th .ebl extension) you should see a syntaxt highlighted specification. For instance, open the `examples/simple_transaction/Account.ebl` file in the `rebel-core` project.

### Simulation and checking using Z3
The Rebel simulator and model checker us the Microsoft Z3 SMT solver. Therefor the solver must be installed on the local system.

#### Steps
* Install the Microsoft Z3 SMT solver. Go to https://github.com/Z3Prover/z3 and follow the instructions
* Change your eclipse.ini and add the following parameter: `-Dsolver.z3.path=<path to your local z3 installation>`
* Restart Eclipse

Now the intergration with the Z3 solver should work. You can test this by opening a Rebel test file (with the .tebl extension). For instance, open the `examples/simple_transaction/TransactionTest.tebl` file in the `rebel-core` project. Select  a `check` statement and open the context menu by hitting the right mouse button. Select the `Rebel-actions -> Check` option. If the integration with the solver works you should see a dialog showing that the check is satisfiable or not.

## Troubleshooting
Rebel is used for a ongoing research project conducted at ING and CWI. It is far from stable. If you run into trouble please leave us a comment and we will try to help you! You can also create an issue and we'll try to fix it.