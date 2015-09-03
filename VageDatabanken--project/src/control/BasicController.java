package control;

import car.VehicleProperties;

/**
 * @author jnieland
 */
public class BasicController implements Controller{

    public BasicController(){

    }

    @Override
    public FrameControl getFrameControl(VehicleProperties vp) {

        float steering = 0f, acceleration = 0f, brake = 0f;

        float minSensorDistance = Math.min(vp.getDistanceFromFrontSensor(), Math.min(vp.getDistanceFromLeftSensor(), vp.getDistanceFromRightSensor()));
        if( vp.getCurrentCarSpeedKph() < 150) {
            acceleration = 1600;
        }

        if(vp.getDistanceFromLeftSensor() == minSensorDistance && vp.getDistanceFromLeftSensor() < 15) {
            //steer to the right a bit
            steering = .5f;
        } else if(vp.getDistanceFromRightSensor() == minSensorDistance && vp.getDistanceFromRightSensor() < 15) {
            steering = -.5f;
        }

        //braking when getting close
        if(vp.getDistanceFromFrontSensor()<50 && vp.getCurrentCarSpeedKph()>100) {
            acceleration = 0;
            brake = 40f;
        }

        //keep the scanangle from the previous frame
        FrameControl fc = new FrameControl(steering, acceleration, brake, vp.getScanAngle());

        return fc;
    }
}
