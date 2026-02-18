import { defineConfig } from "eslint/config";

export default defineConfig([
	{
		files: ["support/"],
		rules: {
			"no-unused-vars": "off",
		},
	},
]);
