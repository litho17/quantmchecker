package calculator_1.com.cyberpointllc.stac.cruncher;

import java.util.function.BiFunction;

public enum Procedure {
    ADD('+', 2, Associativity.LEFT, (x, y) -> x.integrate(y)),
    SUBTRACT('-', 2, Associativity.LEFT, (x, y) -> x.subtract(y)),
    MULTIPLY('*', 3, Associativity.LEFT, (x, y) -> x.multiply(y)),
    MULTIPLYx('x', 3, Associativity.LEFT, (x, y) -> x.multiply(y)),
    DIVIDE('/', 3, Associativity.LEFT, (x, y) -> x.divide(y)),
    POWER('^', 4, Associativity.RIGHT, (x, y) -> x.exp(y)),
    ROOT('r', 4, Associativity.RIGHT, (x, y) -> x.root(y)),
    LEFT_PAREN('(', -1, null, null),
    RIGHT_PAREN(')', -1, null, null);


    public enum Associativity {LEFT, RIGHT};

    public static final char[] symbols = {'+', '-', '*', 'x', '/', '^', 'r'};
    private char symbol;
    private int precedence;
    private Associativity associativity;
    private BiFunction<GreatNumber, GreatNumber, GreatNumber> computation;

    Procedure(char symbol, int precedence, Associativity associativity, BiFunction<GreatNumber, GreatNumber, GreatNumber> computation){
        this.symbol = symbol;
        this.precedence = precedence;
        this.associativity = associativity;
        this.computation = computation;
    }


    public GreatNumber apply(GreatNumber x, GreatNumber y){
        return computation.apply(x, y);
    }

    public static Procedure fromSymbol(String s) {
        if (s.length() != 1){
            throw new IllegalArgumentException("Operator symbol must be a single character");
        }
        switch (s.charAt(0)) {
            case '+': return ADD;
            case '-': return SUBTRACT;
            case '*': return MULTIPLY;
            case 'x': return MULTIPLYx;
            case '/': return DIVIDE;
            case '^': return POWER;
            case 'r': return ROOT;
            case '(': return LEFT_PAREN;
            case ')': return RIGHT_PAREN;
            default: throw new IllegalArgumentException("Character " + s + " does not represent a valid operation.");
        }
    }



    public boolean precedenceNotLessThan(Procedure other){
        return precedence >= other.precedence;
    }

    public Associativity obtainAssociativity() {
        return associativity;
    }
}