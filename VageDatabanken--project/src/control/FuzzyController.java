package control;

import car.VehicleProperties;

import net.sourceforge.jFuzzyLogic.FIS;
import net.sourceforge.jFuzzyLogic.plot.JFuzzyChart;


/**
 * @author @tnnaesse
 * @author @nvhaver
 */

public abstract class FuzzyController implements Controller {

    private FIS fis;

    public FuzzyController(String flcFileName) {
        super();

        // Load from 'FCL' file
        fis = FIS.load(flcFileName, true);

        // Error while loading?
        if(fis == null) {
            System.err.println("Can't load file: '" + flcFileName + "'");
        }

        JFuzzyChart.get().chart(fis);
    }

    @Override
    public FrameControl getFrameControl(VehicleProperties vp) {

        float currentRoadWidth = vp.getCurrentRoadWidth();
        float frontSensorDistance = vp.getDistanceFromFrontSensor();
        float leftSensorDistance  = vp.getDistanceFromLeftSensor();
        float rightSensorDistance = vp.getDistanceFromRightSensor();

        // If left > right, there is a left corner incoming.
        // Also normalise the value to account for all kinds of corners
        float corner = (rightSensorDistance - leftSensorDistance) / (leftSensorDistance + rightSensorDistance);

        fis.setVariable("carSpeedKph", vp.getCurrentCarSpeedKph());
        fis.setVariable("frontSensorDistance", frontSensorDistance);
        fis.setVariable("lateralVelocity", vp.getLateralVelocity());
        fis.setVariable("corner", corner);

        fis.evaluate(); // Evaluate

        FrameControl fc = new FrameControl(
                (float) fis.getVariable("steering").getValue(),
                (float) fis.getVariable("acceleration").getValue(),
                (float) fis.getVariable("brake").getValue(),
                Math.toRadians((float) fis.getVariable("scanangle").getValue()));

        System.out.format("FD: %6.2f ",vp.getDistanceFromFrontSensor());
        System.out.format("CO: %6.2f ",corner);
        System.out.format("LD: %6.2f ",vp.getDistanceFromLeftSensor());
        System.out.format("RD: %6.2f ",vp.getDistanceFromRightSensor());
        System.out.format("SP: %6.2f ",vp.getCurrentCarSpeedKph());
        System.out.format("AC: %7.2f ",fis.getVariable("acceleration").getValue());
        System.out.format("BR: %5.2f ",fis.getVariable("brake").getValue());
        System.out.format("LV: %6.2f ",vp.getLateralVelocity());
        System.out.format("ST: %6.2f ",fis.getVariable("steering").getValue());
        System.out.println();

        return fc;
    }
}
