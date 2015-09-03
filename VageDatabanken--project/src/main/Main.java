package main;

import car.RaceCar;
import control.Controller;
import control.SafeController;
import control.BasicController;
import control.DriftController;
import control.SpeedController;

/**
 * Loader for the project. Define your own controller, set username, track and manual control to launch a run.
 *
 * @author jnieland
 */
public class Main {

    public static void main(String[] args) {
    /**
     * Start a run with given settings: - username: used for statistics, see http://telin.ugent.be/~jnieland/scores.php for
     * the leaderboard - trackname: possible values are: - spafrancorchamps1024 - silverstone1024 - interlagos1024 - texas1024
     * - controller, written by you - manual control, only non-manual laps are recorded for the leaderboard
     */

    Controller controller = new DriftController();
    String trackname = "interlagos1024";

    RaceCar app = new RaceCar("nondefaultname", trackname, controller, false);
    app.start();
    }

}
