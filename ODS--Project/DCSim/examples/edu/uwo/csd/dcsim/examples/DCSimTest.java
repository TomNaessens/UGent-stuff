package edu.uwo.csd.dcsim.examples;

import java.util.ArrayList;

import org.apache.log4j.Logger;

import edu.uwo.csd.dcsim.*;
import edu.uwo.csd.dcsim.application.Applications;
import edu.uwo.csd.dcsim.application.InteractiveApplication;
import edu.uwo.csd.dcsim.application.sla.InteractiveServiceLevelAgreement;
import edu.uwo.csd.dcsim.application.workload.*;
import edu.uwo.csd.dcsim.common.SimTime;
import edu.uwo.csd.dcsim.core.Simulation;
import edu.uwo.csd.dcsim.host.Host;
import edu.uwo.csd.dcsim.host.HostModels;
import edu.uwo.csd.dcsim.host.resourcemanager.DefaultResourceManagerFactory;
import edu.uwo.csd.dcsim.host.scheduler.DefaultResourceSchedulerFactory;
import edu.uwo.csd.dcsim.management.AutonomicManager;
import edu.uwo.csd.dcsim.management.capabilities.*;
import edu.uwo.csd.dcsim.management.events.VmPlacementEvent;
import edu.uwo.csd.dcsim.management.policies.*;
import edu.uwo.csd.dcsim.vm.VmAllocationRequest;


public class DCSimTest extends SimulationTask {

	private static Logger logger = Logger.getLogger(DCSimTest.class);
	
	public static void main(String args[]) {
	
		Simulation.initializeLogging();
		
		SimulationTask task = new DCSimTest("AppExample", SimTime.days(10));
		
		task.run();
		
		task.getMetrics().printDefault(logger);
		
	}
	
	public DCSimTest(String name, long duration) {
		super(name, duration);
		this.setMetricRecordStart(SimTime.minutes(10));
		this.setRandomSeed(6662890007189740306l);
	}

	@Override
	public void setup(Simulation simulation) {
		
		DataCentre dc = new DataCentre(simulation);
                
                
		int aantalHosts = 4;

	        int hostPrivCpu = 500;  // Cynric - waarop gebaseerd?
	        int hostPrivBW  = 1280; // Cynric - idem?
	        
	        int aantalVMs   = 8;    // Cynric - waarop gebaseerd?
	        int VMcores     = 1;	// Cynric - VM 16 cores? nee toch, de host/node zelf?
	        int VMcpu	= 2400; // Cynric - idem?
	        int VMram 	= 512;  // Cynric - idem?
	
	        int VMbw 	= 12800/(16/VMcores); // Cynric - wat is het verschil met hostPrivBW?
	        int VMstorage	= 2048;
	        double VMtime   = 0.01; // Cynric - waarop gebaseerd?
	        //double utilScale=0.98;  // Cynric - opnieuw, waarop gebaseerd? 
	        
	        //double[] cpuUtilization={0.5,0.9,0.85};		// lower, upper, and target CPU utilization in de hosts
														// Cynric - opnieuw, waarop gebaseerd?
	
	        //int relocPolicy=30; 	//om de hoeveel minuten de relocation policy wordt uitgevoerd
	        //int consolPolicy=60; 	//om de hoeveel minutes de consolidation policy wordt uitgevoerd
								// Cynric - maakt niet veel uit voor ons
                
		// Add the DataCentre to the simulation
		simulation.addDatacentre(dc);
		
		// Create the HostPoolManager capability separately, as we need to reference it later to add hosts
		HostPoolManager hostPool = new HostPoolManager();
		
		// Create a new AutonomicManager with this capability
		AutonomicManager dcAM = new AutonomicManager(simulation, hostPool);
		
		// Install the HostStatusPolicy and VmPlacementPolicy
		dcAM.installPolicy(new HostStatusPolicy(5));
		
		//hier kiezen welke placement policy
		dcAM.installPolicy(new DefaultVmPlacementPolicy());
		//dcAM.installPolicy(new VWallPlacementPolicy());
		
		// Create hosts
		Host.Builder hostBuilder = HostModels.VirtualWallHost(simulation)
									.privCpu(hostPrivCpu)
									.privBandwidth(hostPrivBW)
									.resourceManagerFactory(new DefaultResourceManagerFactory())
									.resourceSchedulerFactory(new DefaultResourceSchedulerFactory());
		
		// Instantiate the Hosts
		ArrayList<Host> hosts = new ArrayList<Host>();
		for (int i = 0; i < aantalHosts; ++i) {
			Host host = hostBuilder.build();
			
			// Create an AutonomicManager for the Host, with the HostManager capability (provides access to the host being managed)
			AutonomicManager hostAM = new AutonomicManager(simulation, new HostManager(host));
			
			// Install a HostMonitoringPolicy, which sends status updates to the datacentre manager, set to execute every 5 minutes
			// Cynric - waarop zijn deze vijf minuten gebaseerd?
			hostAM.installPolicy(new HostMonitoringPolicy(dcAM), SimTime.minutes(5), 0);
			
			// Install a HostOperationsPolicy, which handles basic host operations
			hostAM.installPolicy(new HostOperationsPolicy());
			
			// Optionally, we can "install" the manager into the Host. This ensures that the manager does not run when the host is
			// not 'ON', and triggers hooks in the manager and policies on power on and off.
			host.installAutonomicManager(hostAM);

			// Add the Host to the DataCentre
			dc.addHost(host);
			
			// Add the Host to the HostPoolManager capability of our datacentre AutonomicManager
			hostPool.addHost(host, hostAM);
			
			hosts.add(host);
		}
		
		//Create applications
		ArrayList<VmAllocationRequest> vmRequests = new ArrayList<VmAllocationRequest>();
		
		for (int i = 0; i < aantalVMs; ++i) {
			// We gebruiken geen trace aangezien we er geen geschikte hebben, we gebruik een static workload.
			StaticWorkload workload = new StaticWorkload(simulation);
			workload.setWorkLevel(100); //anders had ik geen throughput?
            
			InteractiveApplication app = Applications.singleTaskInteractiveApplication(simulation, workload, VMcores, VMcpu, VMram, VMbw, VMstorage, VMtime);
                        			
			InteractiveServiceLevelAgreement sla = new InteractiveServiceLevelAgreement(app).responseTime(1, 1); // sla limit at 1s response time
			app.setSla(sla);
			
			//place applications
			vmRequests.addAll(app.createInitialVmRequests());

		}
		
		VmPlacementEvent vmPlacementEvent = new VmPlacementEvent(dcAM, vmRequests);
		simulation.sendEvent(vmPlacementEvent, 0);
	}	
}
