// @ts-check
import { defineConfig } from "astro/config";
import starlight from "@astrojs/starlight";
import catppuccin from "@catppuccin/starlight";

// https://astro.build/config
export default defineConfig({
	site: "https://huub.solutions/",
	integrations: [
		// https://starlight.astro.build/reference/configuration
		starlight({
			title: "Huub",
			social: [
				{
					icon: "github",
					label: "GitHub",
					href: "https://github.com/huub-solver/huub",
				},
			],
			editLink: {
				baseUrl: "https://github.com/huub-solver/huub/edit/develop/docs/",
			},
			favicon: "/favicon.ico",
			pagefind: false,
			sidebar: [],
			customCss: ["./src/styles/fonts.css"],
			plugins: [
				catppuccin({
					light: { accent: "blue" },
					dark: { accent: "blue" },
				}),
			],
		}),
	],
});
