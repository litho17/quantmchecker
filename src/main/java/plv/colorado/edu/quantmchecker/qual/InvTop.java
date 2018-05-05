package plv.colorado.edu.quantmchecker.qual;

import org.checkerframework.framework.qual.*;

import java.lang.annotation.*;

/**
 * @author Tianhan Lu
 */
@DefaultQualifierInHierarchy
@InvisibleQualifier
@SubtypeOf({})
@Documented
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
@DefaultFor({TypeUseLocation.RETURN, TypeUseLocation.IMPLICIT_LOWER_BOUND})
@ImplicitFor(literals = LiteralKind.NULL, typeNames = java.lang.Void.class)
public @interface InvTop {}
