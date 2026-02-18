export default {
  plugins: [
    "remark-lint",
    "remark-gfm",
    "remark-preset-lint-recommended",

    // Allow bare URLs
    ["remark-lint-no-literal-urls", false],

    // Require a loose list if any item spans multiple lines;
    // otherwise require a tight list
    "remark-lint-list-item-spacing",
  ],
}
