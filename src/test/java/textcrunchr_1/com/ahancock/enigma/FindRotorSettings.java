package textcrunchr_1.com.ahancock.enigma;

import plv.colorado.edu.quantmchecker.qual.Inv;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Scanner;

public class FindRotorSettings {

    // Tunable constants
    private static final int ERRORS_ALLOWED = 4;

    private static final double MULTIPLIER = 1.0;

    private static final int NUMBER_OF_LINES = 3;

    public static void main(String[] args) throws FileNotFoundException {
        // Save the current time to compute total run time.
        long startTime = System.currentTimeMillis();
        // Read three lines from the source file
        @Inv("i+<self>=+26-24") String cipherText = new  String();
        Scanner scanner = new  Scanner(new  File(args[0]));
        c24: for (int i = 0; i < NUMBER_OF_LINES; i++) {
            // Preserve the newline from the source text
            c26: cipherText += scanner.nextLine() + "\n";
        }
        scanner.close();
        EnigmaMachine machine = EnigmaFactory.buildEnigmaMachine();
        English english = new  English(ERRORS_ALLOWED, MULTIPLIER);
        // Loop through all possible combinations for a three Rotor machine
        for (int _i = 0; _i < Symbol.MAX; _i++) for (int j = 0; j < Symbol.MAX; j++) for (int k = 0; k < Symbol.MAX; k++) {
            // Set the machine to the current Rotor positions
            machine.setRotors(_i, j, k);
            // Attempt to decode the ciphertext
            String plainText;
            plainText = machine.encodeLine(cipherText);
            // Add the plainText to the English class to analyze
            // frequency
            english.add(plainText);
            if (english.isEnglish()) {
            }
            // Reset the state of the English class
            english.reset();
        }
        // Print the total execution time of the program
        System.out.println("Execution time:" + (System.currentTimeMillis() - startTime) + " ms");
    }
}
