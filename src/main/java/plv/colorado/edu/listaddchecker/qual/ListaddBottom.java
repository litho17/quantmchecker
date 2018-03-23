package plv.colorado.edu.listaddchecker.qual;

import org.checkerframework.framework.qual.ImplicitFor;
import org.checkerframework.framework.qual.LiteralKind;
import org.checkerframework.framework.qual.SubtypeOf;
import plv.colorado.edu.quantmchecker.qual.ListInv;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Target;

/**
 * @author Tianhan Lu
 */
@SubtypeOf({ListaddTop.class})
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
@ImplicitFor(literals= LiteralKind.NULL)
@Documented
public @interface ListaddBottom {}
