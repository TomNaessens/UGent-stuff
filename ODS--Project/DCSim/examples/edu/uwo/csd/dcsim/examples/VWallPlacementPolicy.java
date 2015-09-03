package edu.uwo.csd.dcsim.management.policies;

import java.util.ArrayList;
import java.util.Collection;

import edu.uwo.csd.dcsim.host.Resources;
import edu.uwo.csd.dcsim.management.*;
import edu.uwo.csd.dcsim.management.action.InstantiateVmAction;
import edu.uwo.csd.dcsim.management.capabilities.HostPoolManager;
import edu.uwo.csd.dcsim.management.events.ShutdownVmEvent;
import edu.uwo.csd.dcsim.management.events.VmPlacementEvent;
import edu.uwo.csd.dcsim.vm.VmAllocationRequest;

/**
 * VWallPlacementPolicy plaatst de VMs op de host die nog de meeste resources ter beschikking heeft
 */
public class VWallPlacementPolicy extends Policy {

	public VWallPlacementPolicy() {
		addRequiredCapability(HostPoolManager.class);
	}
		
	public void execute(VmPlacementEvent event) {

		HostPoolManager hostPool = manager.getCapability(HostPoolManager.class);
		
		//filter out invalid host status
		Collection<HostData> hosts = new ArrayList<HostData>(); 
		for (HostData host : hostPool.getHosts()) {
			if (host.isStatusValid()) {
				hosts.add(host);
			}
		}
		
		//reset the sandbox host status to the current host status
		for (HostData host : hosts) {
			host.resetSandboxStatusToCurrent();
		}
		
		//iterate though each VM to place
		for (VmAllocationRequest vmAllocationRequest : event.getVMAllocationRequests()) {
			HostData allocatedHost = null;
			
			Resources reqResources = new Resources();
                        reqResources.setCpu(vmAllocationRequest.getCpu());
                        reqResources.setMemory(vmAllocationRequest.getMemory());
                        reqResources.setBandwidth(vmAllocationRequest.getBandwidth());
                        reqResources.setStorage(vmAllocationRequest.getStorage());
                        //alle hosts die voldoende capaciteit hebben aan de ArrayList availableHosts toevoegen zodat we hier achteraf
                        //de host uit kunnen selecteren die nog meeste resource over heeft
                        ArrayList<HostData> availableHosts = new ArrayList<HostData>(); 
			for (HostData target : hosts) {
                            if (HostData.canHost(vmAllocationRequest.getVMDescription().getCores(), 
                                            vmAllocationRequest.getVMDescription().getCoreCapacity(), 
                                            reqResources,
                                            target.getSandboxStatus(),
                                            target.getHostDescription())) {	//target has capability and capacity to host VM


                                availableHosts.add(target);
                                //break;
                             } 
			}
                        //beste target host selecteren (op basis van bezette cores en cpu shares (initieel draait er overal al 1 core de VMM)
                        HostData target=null;
                        int meesteCoreCapacity=-1;
                        for (HostData eenTargetKandidaat : availableHosts) {
                            Resources resourcesInUse=eenTargetKandidaat.getSandboxStatus().getResourcesInUse();
                            Resources resourcesHost=eenTargetKandidaat.getHostDescription().getResourceCapacity();
                            int coreCapacityTerBeschikking=resourcesHost.getCoreCapacity() - resourcesInUse.getCoreCapacity();
                                    
                            if(coreCapacityTerBeschikking > meesteCoreCapacity){ //betere host kandidaat gevonden
                                target=eenTargetKandidaat;
                                meesteCoreCapacity=coreCapacityTerBeschikking;
                            }
                        }
                        
                        //vanaf hier zelfde principe als DefaultVmPlacementPolicy
                        allocatedHost = target;
                        
                        //add a dummy placeholder VM to keep track of placed VM resource requirements
                        target.getSandboxStatus().instantiateVm(
                                        new VmStatus(vmAllocationRequest.getVMDescription().getCores(),
                                        vmAllocationRequest.getVMDescription().getCoreCapacity(),
                                        reqResources));

                        //invalidate this host status, as we know it to be incorrect until the next status update arrives
                        target.invalidateStatus(simulation.getSimulationTime());
			
			if (allocatedHost != null) {
				InstantiateVmAction instantiateVmAction = new InstantiateVmAction(allocatedHost, vmAllocationRequest, event);
				instantiateVmAction.execute(simulation, this);
			} else {
				event.addFailedRequest(vmAllocationRequest); //add a failed request to the event for any event callback listeners to check
			}
		}
	}
	
	public void execute(ShutdownVmEvent event) {
		HostPoolManager hostPool = manager.getCapability(HostPoolManager.class);
		AutonomicManager hostManager = hostPool.getHost(event.getHostId()).getHostManager();
		
		//mark host status as invalid
		hostPool.getHost(event.getHostId()).invalidateStatus(simulation.getSimulationTime());
		
		//prevent the original event from logging, since we are creating a new event to forward to the host
		event.setLog(false);
		
		ShutdownVmEvent shutdownEvent = new ShutdownVmEvent(hostManager, event.getHostId(), event.getVmId()); 
		event.addEventInSequence(shutdownEvent);
		simulation.sendEvent(shutdownEvent);
	}

	@Override
	public void onInstall() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void onManagerStart() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void onManagerStop() {
		// TODO Auto-generated method stub
		
	}
	
}
