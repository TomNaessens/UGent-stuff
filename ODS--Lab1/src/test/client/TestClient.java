package test.client;

import be.ugent.intec.ibcn.ods.rmi.exception.ODSRMIException;
import be.ugent.intec.ibcn.ods.rmi.handler.RemoteReferenceModule;
import be.ugent.intec.ibcn.ods.rmi.handler.filter.GZipFilter;
import be.ugent.intec.ibcn.ods.rmi.net.Client;
import java.io.IOException;
import java.util.Date;

import test.common.Counter;
import test.common.TestService;

/**
 * Sample client
 *
 * 1. create a RemoteReferenceModule 2. call a method 3. call a method which returns
 * another exported object 4. call a method in the "another exported object" 5.
 * call a method which throws an exception (HomeWork). *
 */
public class TestClient {

    @SuppressWarnings("serial")
    public static void main(String... args) throws ODSRMIException {

        long init = new Date().getTime();
        System.out.println("Creating CallHandler");
        RemoteReferenceModule callHandler = new RemoteReferenceModule();
        try {
            System.out.println("Creating Client");
            Client client = new Client("localhost", 1234, callHandler, new GZipFilter());


            System.out.println("Getting proxy");
            TestService myServiceCaller = (TestService) client.getGlobal(TestService.class);

            System.out.println("Calling the method sayHello():");
            System.out.println("return: " + myServiceCaller.sayHello("Stijn"));

            System.out.println("Calling the method getCounter():");
            Counter counter = myServiceCaller.getCounter();
            System.out.println("return: " + counter);

            System.out.println("Counter::getNumber(): " + counter.getNumber());

            //HomeWork - Exception handling
            System.out.println("Calling the method throwAnExceptionPlease():");
            myServiceCaller.throwAnExceptionPlease();

            client.close();
        } catch (IOException e) {
        }

        System.out.println("Time: " + (new Date().getTime() - init));

    }
}
