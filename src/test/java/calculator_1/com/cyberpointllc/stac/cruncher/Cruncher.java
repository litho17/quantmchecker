package calculator_1.com.cyberpointllc.stac.cruncher;

import plv.colorado.edu.quantmchecker.qual.InvUnk;

import java.text.ParseException;
import java.util.EmptyStackException;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Stack;

public class Cruncher {

    private Stack<Procedure> procedures = new Stack<>();
    private CruncherFormatter formatter;
    private String procedurePattern = "()+-*/r^x";
    public Cruncher(CruncherFormatter formatter) {
        this.formatter = formatter;

        if (formatter instanceof RomanNumeralFormatter) {
            this.procedurePattern = "()+-*/r^";
            }
    }

    // We process infix expressions using +, -, / (division), x (multiplication), r (for root, where x r n is the nth root of x), and ^ (exponentiation)
    public String processEquation(String equation) {
        // remove spaces
        equation = equation.replace(" ", "");
        try {
            String chunk;
            int index = 0;
            int lastIndex = 0;
            boolean first = true;
            LinkedList<Object> outcome = new LinkedList<>();

            while ((index = takeNextProcedure(equation, lastIndex)) != -1) {
                lastIndex = index;
                if (first) {
                    Searcher searcher = new Searcher();
                    chunk = searcher.fetchNextIntChunk(equation.substring(0, index), 0);
                    if (!chunk.trim().isEmpty()){
                        outcome = processCount(chunk.trim(), outcome);
                    }
                    first = false;
                }
                String procedure = equation.substring(index, index+1);
                lastIndex++;

                outcome = processProcedure(procedure, outcome);

                Searcher searcher = new Searcher();
                chunk = searcher.fetchNextIntChunk(equation, lastIndex);
                if (!chunk.isEmpty()) {

                    if (searcher.startIndex == lastIndex ) {
                        outcome = processCount(chunk.trim(), outcome);
                    }
                    else { // if we skipped operators in the process, skip this for now
                        //System.out.println(expression.substring(lastIndex - 1));
                        continue;
                    }
                }
                lastIndex += chunk.length();
            }
            // get last chunk if there is one
            chunk = equation.substring(lastIndex, equation.length());
            if (!chunk.trim().isEmpty()) {
                try {
                    outcome = processProcedure(chunk.trim(), outcome);
                } catch (Exception e) {
                    outcome = processCount(chunk.trim(), outcome);
                } finally {
                    // this is ok
                }
            }

            while (!procedures.empty()) {
                Procedure top = procedures.pop();
                outcome.add(top);
            }

            GreatNumber out = processOutcome(outcome);

            return formatter.format(out);
        } catch (@InvUnk("Extend library class") ReportTooGreatDeviation rtle) {
            throw rtle;
        } catch (EmptyStackException ese) {
            throw new InvalidEquationDeviation("Expression " + equation + " is invalid: " + ese);
        } catch (NumberFormatException nfe) {
            throw new InvalidEquationDeviation("Expression " + equation + " is invalid: " + nfe);
        }
    }

    public String processEquation(String equation, CruncherFormatter formatter) {
        // remove spaces
        equation = equation.replace(" ", "");

        try {
            String chunk;
            int index = 0;
            int lastIndex = 0;
            boolean first = true;
            LinkedList<Object> outcome = new LinkedList<>();

            while ((index = takeNextProcedure(equation, lastIndex)) != -1) {
                lastIndex = index;
                if (first) {
                    Searcher searcher = new Searcher();
                    chunk = searcher.fetchNextIntChunk(equation.substring(0, index), 0);
                    if (!chunk.trim().isEmpty()){
                        outcome = processCount(chunk.trim(), outcome);
                    }
                    first = false;
                }
                String procedure = equation.substring(index, index+1);
                lastIndex++;

                outcome = processProcedure(procedure, outcome);

                Searcher searcher = new Searcher();
                chunk = searcher.fetchNextIntChunk(equation, lastIndex);
                if (!chunk.isEmpty()) {

                    if (searcher.startIndex == lastIndex ) {
                        outcome = processCount(chunk.trim(), outcome);
                    }
                    else { // if we skipped operators in the process, skip this for now
                        //System.out.println(expression.substring(lastIndex - 1));
                        continue;
                    }
                }
                lastIndex += chunk.length();
            }
            // get last chunk if there is one
            chunk = equation.substring(lastIndex, equation.length());
            if (!chunk.trim().isEmpty()) {
                try {
                    outcome = processProcedure(chunk.trim(), outcome);
                } catch (Exception e) {
                    outcome = processCount(chunk.trim(), outcome);
                } finally {
                    // this is ok
                }
            }

            while (!procedures.empty()) {
                Procedure top = procedures.pop();
                outcome.add(top);
            }

            GreatNumber out = processOutcome(outcome);

            return formatter.format(out);
        } catch (@InvUnk("Extend library class") ReportTooGreatDeviation rtle) {
            throw rtle;
        } catch (EmptyStackException ese) {
            throw new InvalidEquationDeviation("Expression " + equation + " is invalid: " + ese);
        } catch (NumberFormatException nfe) {
            throw new InvalidEquationDeviation("Expression " + equation + " is invalid: " + nfe);
        }
    }

    private int takeNextProcedure(String s, int start) {
        for (int b = start; b <s.length(); b++){
            if (procedurePattern.indexOf(s.charAt(b)) >= 0) {
                return b;
            }
        }
        return -1;
    }

    private class Searcher {
        int startIndex = -1;
        int endIndex = -1;

        private String fetchNextIntChunk(String s, int start) {
            String chunk = "";
            String validCharacters = formatter.takeValidCharacters();
            for (int i=start; i<s.length(); i++){
                if (validCharacters.indexOf(s.charAt(i)) >= 0){
                    chunk += s.charAt(i);
                    if (startIndex == -1) {
                        startIndex = i;
                    }
                } else if (procedurePattern.indexOf(s.charAt(i)) >= 0) {
                    if (!chunk.isEmpty()){
                        endIndex = i-1;
                        return chunk;
                    } // else keep looking
                } else {
                    throw new InvalidEquationDeviation("Expression " + s + " is invalid: Expression may only contain valid characters");
                }
            }
            endIndex = s.length()-1;
            return chunk;
        }
    }
    // the following two methods modify the expression to postfix form

    private LinkedList<Object> processCount(String countStr, LinkedList<Object> outcome) {
        try {
            GreatNumber count = (GreatNumber)formatter.parseObject(countStr);
            outcome.add(count);

            return outcome;
        } catch (ParseException pe) {
            throw new InvalidEquationDeviation("Expression " + countStr + " is invalid: Error while attempting to parse at index " + pe.getErrorOffset());
        }
    }

    private LinkedList<Object> processProcedure(String procedureSymbol, LinkedList<Object> outcome) {
        Procedure procedure = Procedure.fromSymbol(procedureSymbol);
        if (Procedure.LEFT_PAREN.equals(procedure)) {
            procedures.push(procedure);
            outcome.add(procedure);
        } else if (Procedure.RIGHT_PAREN.equals(procedure)) {
            while (!procedures.empty() && !procedures.peek().equals(Procedure.LEFT_PAREN)) {
                Procedure top = procedures.pop();
                outcome.add(top);
            }

            procedures.pop(); // pop the left paren
            outcome.add(procedure);
        } else {
            Procedure top;
            while (!procedures.empty() && procedures.peek().precedenceNotLessThan(procedure) && !procedure.obtainAssociativity().equals(Procedure.Associativity.RIGHT)) {
                top = procedures.pop();
                outcome.add(top);
            }
            procedures.push(procedure);
        }

        return outcome;
    }

    // this method processes the postfix stack to compute the answer
    private GreatNumber processOutcome(Queue<?> queue){
        @InvUnk("Bug!") Stack<GreatNumber> operandStack = new Stack<>();

        while (queue.size() > 0) {
            Object next = queue.remove();

            if (next instanceof Procedure) {
                Procedure procedure = (Procedure) next;

                if (procedure.equals(Procedure.LEFT_PAREN)) {
                    @InvUnk("Bug!") LinkedList<Object> tempQueue = new LinkedList<>();
                    int count = 1;

                    while (!queue.isEmpty() && count > 0) {
                        Object obj = queue.remove();

                        if (obj.equals(Procedure.LEFT_PAREN)) {
                            count ++;
                        } else {
                            if (obj.equals(Procedure.RIGHT_PAREN)) {
                                count --;
                            }
                        }

                        if (count > 0) { // Offer everything but the last right parenthesis
                            tempQueue.offer(obj);
                        }
                    }

                    if (count == 0) {
                        GreatNumber tempSolution = processOutcome(tempQueue);
                        operandStack.push(tempSolution);
                    } else {
                        throw new InvalidEquationDeviation("Output processing error: One or more unmatched parentheses");
                    }
                } else {
                    if (operandStack.size() >= 2) {
                        GreatNumber operand2 = operandStack.pop();
                        GreatNumber operand1 = operandStack.pop();
                        operand1 = procedure.apply(operand1, operand2);
                        operandStack.push(operand1);
                    } else {
                        throw new InvalidEquationDeviation("Output processing error: Not enough operands to perform " + procedure);
                    }
                }
            } else {
                GreatNumber operand = (GreatNumber) next;
                operandStack.push(operand);
            }
        }

        return operandStack.pop();
    }
}
