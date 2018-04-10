package plv.colorado.edu.quantmchecker.qual;

import org.checkerframework.framework.qual.SubtypeOf;

import java.lang.annotation.*;

/**
 * @author Tianhan Lu
 */
@SubtypeOf({InvTop.class})
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.LOCAL_VARIABLE, ElementType.FIELD, ElementType.PARAMETER})
@Documented
//Check these qualifiers: package org.checkerframework.framework.qual;
public @interface Inv {
    //@JavaExpression
    public String[] value();
}