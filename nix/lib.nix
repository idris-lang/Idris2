rec {
  # source: https://nixos.org/guides/nix-pills/override-design-pattern.html
  # but with the ability to change the name of the override method
  makeOverridable = kind: f:
    let
      inner = oldArgs:
        (f oldArgs) // {
          ${kind} = newArgs: inner (oldArgs // newArgs);
        };
    in inner;

  # create a flake with overridable options. useful because we can't pass
  # fine-grained overrides to flakes otherwise, we can only change inputs
  # (therefore, this can't change inputs per default, and that should also be unnecessary)
  mkOvrOptsFlake = flakefn: makeOverridable "overrideOptions" flakefn { };
}
